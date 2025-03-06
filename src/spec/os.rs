//! OS-level state machine and OS-level specifications.
//!
//! This is the low-level abstraction of the memory management module, which means some
//! basic structures used by the memory management module are kept, while some implementation
//! details are simplified. This abstraction level performs as a bridge between the concrete
//! implementation and the high level specification.
use vstd::prelude::*;

use super::{
    addr::{PAddr, VAddr, VIdx, WORD_SIZE},
    hl::{HlConstants, HlMemoryState},
    mem::{
        Frame, FrameSize, MapOp, PageTableMem, QueryOp, ReadOp, TLBEvictOp, TLBFillOp, UnmapOp,
        WriteOp,
    },
    nat_to_u64,
    s1pt::page_table_walk,
};

verus! {

/// OS-level Memory State, which includes
///
/// - Common memory: Memory used by the OS and applications.
/// - Page table memory: Memory used to store page tables.
/// - TLB: Translation Lookaside Buffer.
pub struct OSMemoryState {
    /// 8-byte-indexed physical memory.
    pub mem: Seq<nat>,
    /// Page table memory.
    pub pt_mem: PageTableMem,
    /// Translation Lookaside Buffer.
    pub tlb: Map<VAddr, Frame>,
}

/// View(abstraction) functions.
impl OSMemoryState {
    /// Interpret the page table memory as a map (vaddr -> frame).
    pub open spec fn interpret_pt_mem(self) -> Map<VAddr, Frame> {
        let max_vaddr: nat = 0x8000_0000;
        Map::new(
            |addr: VAddr|
                addr.0 < max_vaddr && exists|frame: Frame| #[trigger]
                    page_table_walk(self.pt_mem, nat_to_u64(addr.0), frame),
            |addr: VAddr|
                choose|frame: Frame| #[trigger]
                    page_table_walk(self.pt_mem, nat_to_u64(addr.0), frame),
        )
    }

    /// Collect all page mappings managed by OS memory state (pt_mem and TLB).
    pub open spec fn all_mappings(self) -> Map<VAddr, Frame> {
        Map::new(
            |base: VAddr| self.tlb.contains_key(base) || self.interpret_pt_mem().contains_key(base),
            |base: VAddr|
                {
                    if self.tlb.contains_key(base) {
                        self.tlb[base]
                    } else {
                        self.interpret_pt_mem()[base]
                    }
                },
        )
    }

    /// Interpret the common memory as a map (vidx -> word value).
    pub open spec fn interpret_mem(self) -> Map<VIdx, nat> {
        Map::new(
            |vidx: VIdx|
                exists|base: VAddr, frame: Frame|
                    {
                        &&& #[trigger] self.all_mappings().contains_pair(base, frame)
                        &&& vidx.addr().within(base, frame.size.as_nat())
                    },
            |vidx: VIdx|
                {
                    let (base, frame) = choose|base: VAddr, frame: Frame|
                        {
                            &&& #[trigger] self.all_mappings().contains_pair(base, frame)
                            &&& vidx.addr().within(base, frame.size.as_nat())
                        };
                    self.mem[vidx.addr().map(base, frame.base).idx().as_int()]
                },
        )
    }

    /// High-level (abstract) view of the OS memory state.
    pub open spec fn view(self) -> HlMemoryState {
        HlMemoryState {
            mem: self.interpret_mem(),
            mappings: self.all_mappings(),
            constants: HlConstants { pmem_size: self.mem.len() },
        }
    }
}

/// Helper functions.
impl OSMemoryState {
    /// If exists a mapping that `vaddr` lies in.
    pub open spec fn has_mapping_for(self, vaddr: VAddr) -> bool {
        exists|base: VAddr, frame: Frame| #[trigger]
            self.interpret_pt_mem().contains_pair(base, frame) && vaddr.within(
                base,
                frame.size.as_nat(),
            )
    }

    /// If `frame` overlaps with existing physical memory.
    pub open spec fn overlaps_pmem(self, frame: Frame) -> bool {
        exists|base: VAddr|
            {
                &&& #[trigger] self.interpret_pt_mem().contains_key(base)
                &&& PAddr::overlap(
                    self.interpret_pt_mem()[base].base,
                    self.interpret_pt_mem()[base].size.as_nat(),
                    frame.base,
                    frame.size.as_nat(),
                )
            }
    }

    /// If mapping `(vaddr, frame)` overlaps with existing virtual memory.
    pub open spec fn overlaps_vmem(self, vaddr: VAddr, frame: Frame) -> bool {
        exists|base: VAddr|
            {
                &&& #[trigger] self.interpret_pt_mem().contains_key(base)
                &&& VAddr::overlap(
                    base,
                    self.interpret_pt_mem()[base].size.as_nat(),
                    vaddr,
                    frame.size.as_nat(),
                )
            }
    }
}

/// State Invariants.
impl OSMemoryState {
    /// All frames are within the physical memory bounds.
    pub open spec fn frames_within_pmem(self) -> bool {
        forall|base: VAddr, frame: Frame| #[trigger]
            self.interpret_pt_mem().contains_pair(base, frame) ==> frame.base.offset(
                frame.size.as_nat(),
            ).0 <= self.mem.len()
    }

    /// All frames are 8-byte aligned.
    pub open spec fn frames_aligned(self) -> bool {
        forall|base: VAddr, frame: Frame| #[trigger]
            self.interpret_pt_mem().contains_pair(base, frame) ==> frame.base.aligned(WORD_SIZE)
                && frame.size.as_nat() % WORD_SIZE == 0
    }

    /// Page table mappings do not overlap in virtual memory.
    pub open spec fn mappings_nonoverlap_in_vmem(self) -> bool {
        forall|base1: VAddr, frame1: Frame, base2: VAddr, frame2: Frame|
            self.interpret_pt_mem().contains_pair(base1, frame1)
                && self.interpret_pt_mem().contains_pair(base2, frame2) ==> ((base1 == base2)
                || !VAddr::overlap(base1, frame1.size.as_nat(), base2, frame2.size.as_nat()))
    }

    /// Page table mappings do not overlap in physical memory.
    pub open spec fn mappings_nonoverlap_in_pmem(self) -> bool {
        forall|base1: VAddr, frame1: Frame, base2: VAddr, frame2: Frame|
            self.interpret_pt_mem().contains_pair(base1, frame1)
                && self.interpret_pt_mem().contains_pair(base2, frame2) ==> ((base1 == base2)
                || !PAddr::overlap(
                frame1.base,
                frame1.size.as_nat(),
                frame2.base,
                frame2.size.as_nat(),
            ))
    }

    /// TLB must be a submap of the page table.
    pub open spec fn tlb_is_submap_of_pt(self) -> bool {
        forall|base, frame|
            self.tlb.contains_pair(base, frame)
                ==> #[trigger] self.interpret_pt_mem().contains_pair(base, frame)
    }

    /// OS state invariants.
    pub open spec fn invariants(self) -> bool {
        &&& self.frames_within_pmem()
        &&& self.frames_aligned()
        &&& self.mappings_nonoverlap_in_vmem()
        &&& self.mappings_nonoverlap_in_pmem()
        &&& self.tlb_is_submap_of_pt()
    }
}

/// State transition specifications.
impl OSMemoryState {
    /// Initial memory state.
    ///
    /// The initial state must satisfy the specification.
    pub open spec fn init(self) -> bool {
        &&& self.tlb.dom() === Set::empty()
        &&& self.interpret_pt_mem() === Map::empty()
    }

    /// State transition - Common memory read.
    pub open spec fn read(s1: Self, s2: Self, op: ReadOp) -> bool {
        &&& op.vaddr.aligned(
            WORD_SIZE,
        )
        // Memory, page table and TLB should not be updated
        &&& s1.mem === s2.mem
        &&& s1.pt_mem === s2.pt_mem
        &&& s1.tlb === s2.tlb
        // Check mapping
        &&& match op.mapping {
            Some((base, frame)) => {
                // If `mapping` is `Some`, it should be cached by TLB
                &&& s1.tlb.contains_pair(
                    base,
                    frame,
                )
                // `vaddr` should be in the virtual page mapped by `base`
                &&& op.vaddr.within(
                    base,
                    frame.size.as_nat(),
                )
                // `vaddr` should map to `paddr`
                &&& op.vaddr.map(base, frame.base)
                    === op.paddr
                // Check frame attributes
                &&& if op.vaddr.map(base, frame.base).idx().0 < s1.mem.len() && frame.attr.readable
                    && frame.attr.user_accessible {
                    // The result should be `Ok`
                    &&& op.result is Ok
                    &&& op.result.unwrap() === s1.mem[op.vaddr.map(base, frame.base).idx().as_int()]
                } else {
                    // The result should be `Err`
                    op.result is Err
                }
            },
            None => {
                // If `mapping` is `None`
                &&& !s1.has_mapping_for(
                    op.vaddr,
                )
                // Result should be `Err`
                &&& op.result is Err
            },
        }
    }

    /// State transition - Common memory write.
    pub open spec fn write(s1: Self, s2: Self, op: WriteOp) -> bool {
        &&& op.vaddr.aligned(
            WORD_SIZE,
        )
        // Page table and TLB should not be updated
        &&& s1.pt_mem === s2.pt_mem
        &&& s1.tlb === s2.tlb
        // Check mapping
        &&& match op.mapping {
            Some((base, frame)) => {
                // If `mapping` is `Some`, it should be cached by TLB
                &&& s1.tlb.contains_pair(
                    base,
                    frame,
                )
                // `vaddr` should be in the virtual page mapped by `base`
                &&& op.vaddr.within(
                    base,
                    frame.size.as_nat(),
                )
                // `vaddr` should map to `paddr`
                &&& op.vaddr.map(base, frame.base)
                    === op.paddr
                // Check frame attributes
                &&& if op.vaddr.map(base, frame.base).idx().0 < s1.mem.len() && frame.attr.writable
                    && frame.attr.user_accessible {
                    // The result should be `Ok`
                    &&& op.result is Ok
                    // Update memory
                    &&& s2.mem === s1.mem.update(
                        op.vaddr.map(base, frame.base).idx().as_int(),
                        op.value,
                    )
                } else {
                    // The result should be `Err`
                    &&& op.result is Err
                    // Memory should not be updated
                    &&& s1.mem === s2.mem
                }
            },
            None => {
                // If `mapping` is `None`
                &&& !s1.has_mapping_for(
                    op.vaddr,
                )
                // Result should be `Err`
                &&& op.result is Err
                // Memory should not be updated
                &&& s1.mem === s2.mem
            },
        }
    }

    /// State transition - map a virtual address to a physical frame.
    pub open spec fn map(s1: Self, s2: Self, op: MapOp) -> bool {
        // Memory should not be updated
        &&& s1.mem === s2.mem
        // Base vaddr should align to frame size
        &&& op.vaddr.aligned(
            op.frame.size.as_nat(),
        )
        // Base paddr should align to frame size
        &&& op.frame.base.aligned(
            op.frame.size.as_nat(),
        )
        // Frame should not overlap with existing pmem
        &&& !s1.overlaps_pmem(op.frame)
        // Check vmem overlapping
        &&& if s1.overlaps_vmem(op.vaddr, op.frame) {
            // Mapping fails
            &&& op.result is Err
            // Page table should not be updated
            &&& s1.interpret_pt_mem() === s2.interpret_pt_mem()
        } else {
            // Mapping succeeds
            &&& op.result is Ok
            // Update page table
            &&& s1.interpret_pt_mem().insert(op.vaddr, op.frame) === s2.interpret_pt_mem()
        }
        // s2.tlb is a submap of s1.tlb
        &&& forall|base: VAddr, frame: Frame|
            s2.tlb.contains_pair(base, frame) ==> s1.tlb.contains_pair(base, frame)
    }

    /// State transition - unmap a virtual address.
    pub open spec fn unmap(s1: Self, s2: Self, op: UnmapOp) -> bool {
        // Memory should not be updated
        &&& s1.mem
            === s2.mem
        // Base vaddr should align to some valid frame size
        &&& {
            ||| op.vaddr.aligned(FrameSize::Size4K.as_nat())
            ||| op.vaddr.aligned(FrameSize::Size2M.as_nat())
            ||| op.vaddr.aligned(FrameSize::Size1G.as_nat())
        }
        // Check page table
        &&& if s1.interpret_pt_mem().contains_key(op.vaddr) {
            // Unmapping succeeds
            &&& op.result is Ok
            // Update page table
            &&& s1.interpret_pt_mem().remove(op.vaddr) === s2.interpret_pt_mem()
        } else {
            // Unmapping fails
            &&& op.result is Err
            // Page table should not be updated
            &&& s1.interpret_pt_mem() === s2.interpret_pt_mem()
        }
        // s2.tlb cannot contain any mapping for op.vaddr
        &&& !s2.tlb.contains_key(op.vaddr)
        // s2.tlb is a submap of s1.tlb
        &&& forall|base: VAddr, frame: Frame|
            s2.tlb.contains_pair(base, frame) ==> s1.tlb.contains_pair(base, frame)
    }

    /// State transition - page table query.
    pub open spec fn query(s1: Self, s2: Self, op: QueryOp) -> bool {
        // Memory should not be updated
        &&& s1.mem === s2.mem
        // Base vaddr should align to 8 bytes
        &&& op.vaddr.aligned(
            WORD_SIZE,
        )
        // Page table should not be updated
        &&& s1.pt_mem === s2.pt_mem
        // Check result
        &&& match op.result {
            Ok((base, frame)) => {
                // Page table must contain the mapping
                &&& s1.interpret_pt_mem().contains_pair(base, frame)
                &&& op.vaddr.within(base, frame.size.as_nat())
            },
            Err(_) => {
                // Page table should not contain any mapping for op.vaddr
                !s1.has_mapping_for(op.vaddr)
            },
        }
        // s2.tlb is a submap of s1.tlb
        &&& forall|base: VAddr, frame: Frame|
            s2.tlb.contains_pair(base, frame) ==> s1.tlb.contains_pair(base, frame)
    }

    /// State transition - TLB fill.
    pub open spec fn tlb_fill(s1: Self, s2: Self, op: TLBFillOp) -> bool {
        // Page table must contain the mapping
        &&& s1.interpret_pt_mem().contains_pair(
            op.vaddr,
            op.frame,
        )
        // Insert into tlb
        &&& s2.tlb === s1.tlb.insert(
            op.vaddr,
            op.frame,
        )
        // Memory and page table should not be updated
        &&& s1.mem === s2.mem
        &&& s1.pt_mem === s2.pt_mem
    }

    /// State transition - TLB eviction.
    pub open spec fn tlb_evict(s1: Self, s2: Self, op: TLBEvictOp) -> bool {
        // TLB must contain the mapping
        &&& s1.tlb.contains_key(op.vaddr)
        // Remove from tlb
        &&& s2.tlb === s1.tlb.remove(
            op.vaddr,
        )
        // Memory and page table should not be updated
        &&& s1.mem === s2.mem
        &&& s1.pt_mem === s2.pt_mem
    }
}

} // verus!
