//! High-level state machine & high-level specifications.
//!
//! This is the high-level abstraction of the memory management module, which gives
//! a completely abstract view of the memory state with all implementation details removed.
//!
//! To prove an implementation’s correctness we need to ask what we mean
//! by correctness. The application specification is a state machine encoding our
//! answer to that question.
//!
//! This specification represents the proof target. Our implementation running
//! in the intended environment should refine it. This is demonstrated in part
//! by the proof that the OS-level state machine refines this specification.
use vstd::prelude::*;

use super::{
    addr::{PAddr, VAddr, VIdx, WORD_SIZE},
    mem::{Frame, FrameSize, MapOp, QueryOp, ReadOp, UnmapOp, WriteOp},
};

verus! {

/// High level (abstract) memory state.
pub struct HlMemoryState {
    /// 8-byte-indexed virtual memory.
    ///
    /// We use index rather than address. Addresses that are not aligned to 8-byte boundaries
    /// should not be used to access a value, while indexes don't face this issue.
    pub mem: Map<VIdx, nat>,
    /// Mappings from virtual address to physical frames (virtual page base addr -> physical frame).
    ///
    /// The key must be the base address of a virtual page i.e. virtual range [`key`, `key + frame.size`)
    /// must be mapped to the same physical frame.
    pub mappings: Map<VAddr, Frame>,
    /// Constants.
    pub constants: HlConstants,
}

/// High-level (abstract) memory state constants.
pub struct HlConstants {
    /// Physical memory size (in bytes).
    pub pmem_size: nat,
}

impl HlMemoryState {
    /// Virtual memory domain covered by `self.mappings`.
    pub open spec fn mem_domain_covered_by_mappings(self) -> Set<VIdx> {
        Set::new(
            |vidx: VIdx|
                exists|base: VAddr, frame: Frame|
                    {
                        &&& #[trigger] self.mappings.contains_pair(base, frame)
                        &&& vidx.addr().within(base, frame.size.as_nat())
                    },
        )
    }

    /// If `frame` overlaps with existing physical memory.
    pub open spec fn overlaps_pmem(self, frame: Frame) -> bool {
        exists|base: VAddr|
            {
                &&& #[trigger] self.mappings.contains_key(base)
                &&& PAddr::overlap(
                    self.mappings[base].base,
                    self.mappings[base].size.as_nat(),
                    frame.base,
                    frame.size.as_nat(),
                )
            }
    }

    /// If mapping `(vaddr, frame)` overlaps with existing virtual memory.
    pub open spec fn overlaps_vmem(self, vaddr: VAddr, frame: Frame) -> bool {
        exists|base: VAddr|
            {
                &&& #[trigger] self.mappings.contains_key(base)
                &&& VAddr::overlap(
                    base,
                    self.mappings[base].size.as_nat(),
                    vaddr,
                    frame.size.as_nat(),
                )
            }
    }

    /// If there exists a mapping for `vaddr`.
    pub open spec fn has_mapping_for(self, vaddr: VAddr) -> bool {
        exists|base: VAddr, frame: Frame|
            {
                &&& #[trigger] self.mappings.contains_pair(base, frame)
                &&& vaddr.within(base, frame.size.as_nat())
            }
    }
}

/// State transition specifications.
impl HlMemoryState {
    /// Init state. Empty memory and no mappings.
    pub open spec fn init(self) -> bool {
        &&& self.mem === Map::empty()
        &&& self.mappings === Map::empty()
    }

    /// State transition - Read.
    pub open spec fn read(s1: Self, s2: Self, op: ReadOp) -> bool {
        &&& op.vaddr.aligned(
            WORD_SIZE,
        )
        // Memory and mappings should not be updated
        &&& s1.mappings === s2.mappings
        &&& s1.mem === s2.mem
        // Check mapping
        &&& match op.mapping {
            Some((base, frame)) => {
                // If `mapping` is `Some`, `s1.mappings` should contain it
                &&& s1.mappings.contains_pair(
                    base,
                    frame,
                )
                // `vaddr` should be in the virtual page mapped by `base`
                &&& op.vaddr.within(
                    base,
                    frame.size.as_nat(),
                )
                // Check frame attributes
                &&& if op.vaddr.map(base, frame.base).idx().0 < s1.constants.pmem_size
                    && frame.attr.readable && frame.attr.user_accessible {
                    // The result should be `Ok`
                    &&& op.result is Ok
                    // The value should be the value in the memory at `vidx`
                    &&& op.result.unwrap() === s1.mem[op.vaddr.idx()]
                } else {
                    // The result should be `Err`
                    op.result is Err
                }
            },
            None => {
                // If `mapping` is `None`, the memory domain should not contain `vidx`
                &&& !s1.mem_domain_covered_by_mappings().contains(
                    op.vaddr.idx(),
                )
                // Result should be `Err`
                &&& op.result is Err
            },
        }
    }

    /// State transition - write.
    pub open spec fn write(s1: Self, s2: Self, op: WriteOp) -> bool {
        &&& op.vaddr.aligned(WORD_SIZE)
        // Mappings should not be updated
        &&& s1.mappings === s2.mappings
        // Check mapping
        &&& match op.mapping {
            Some((base, frame)) => {
                // If `mapping` is `Some`, `s1.mappings` should contain it
                &&& s1.mappings.contains_pair(
                    base,
                    frame,
                )
                // `vaddr` should be in the virtual page mapped by `base`
                &&& op.vaddr.within(
                    base,
                    frame.size.as_nat(),
                )
                // Check frame attributes
                &&& if op.vaddr.map(base, frame.base).idx().0 < s1.constants.pmem_size
                    && frame.attr.writable && frame.attr.user_accessible {
                    // The result should be `Ok`
                    &&& op.result is Ok
                    // Memory should be updated at `vidx` with `value`
                    &&& s2.mem === s1.mem.insert(op.vaddr.idx(), op.value)
                } else {
                    // The result should be `Err`
                    &&& op.result is Err
                    // Memory should not be updated
                    &&& s1.mem === s2.mem
                }
            },
            None => {
                // If `mapping` is `None`, the memory domain should not contain `vidx`
                &&& !s1.mem_domain_covered_by_mappings().contains(
                    op.vaddr.idx(),
                )
                // And memory should not be updated
                &&& s1.mem === s2.mem
                // Result should be `Err`
                &&& op.result is Err
            },
        }
    }

    /// State transtion - Map a virtual address to a frame.
    pub open spec fn map(s1: Self, s2: Self, op: MapOp) -> bool {
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
            // Memory and mappings should not be updated
            &&& s1.mem === s2.mem
            &&& s1.mappings === s2.mappings
        } else {
            // Mapping succeeds
            &&& op.result is Ok
            // Update mappings
            &&& s1.mappings.insert(op.vaddr, op.frame)
                === s2.mappings
            // Memory domain should be updated
            &&& s2.mem.dom() === s2.mem_domain_covered_by_mappings()
        }
    }

    /// State transtion - Unmap a virtual address.
    pub open spec fn unmap(s1: Self, s2: Self, op: UnmapOp) -> bool {
        // Base vaddr should align to some valid frame size
        &&& {
            ||| op.vaddr.aligned(FrameSize::Size4K.as_nat())
            ||| op.vaddr.aligned(FrameSize::Size2M.as_nat())
            ||| op.vaddr.aligned(FrameSize::Size1G.as_nat())
        }
        // Check mapping
        &&& if s1.mappings.contains_key(op.vaddr) {
            // Unmapping succeeds
            &&& op.result is Ok
            // Update mappings
            &&& s1.mappings.remove(op.vaddr)
                === s2.mappings
            // Memory domain should be updated
            &&& s2.mem.dom() === s2.mem_domain_covered_by_mappings()
        } else {
            // Unmapping fails
            &&& op.result is Err
            // Memory and mappings should not be updated
            &&& s1.mem === s2.mem
            &&& s1.mappings === s2.mappings
        }
    }

    /// State transition - Page table query.
    pub open spec fn query(s1: Self, s2: Self, op: QueryOp) -> bool {
        // Memory and mappings should not be updated
        &&& s1.mem === s2.mem
        &&& s1.mappings === s2.mappings
        // Check result
        &&& match op.result {
            Ok((base, frame)) => {
                // Must contain the mapping
                &&& s1.mappings.contains_pair(base, frame)
                &&& op.vaddr.within(base, frame.size.as_nat())
            },
            Err(_) => {
                // Should not contain any mapping for op.vaddr
                !s1.has_mapping_for(op.vaddr)
            },
        }
    }
}

} // verus!
