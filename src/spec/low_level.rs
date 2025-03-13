//! Low-level state machine and low-level specifications.
//!
//！The low-level state machine provides a more concrete abstraction of the memory management
//！module, acting as a bridge between the implementation and the high-level specification.
//！
//！The verification assumes that hardware behavior refines the hardware specification. By proving
//！the page table implementation refines the page table specification, we can conclude that the
//！combined system (hardware + hypervisor) refines the low-level specification and, in turn, the
//！high-level specification.
use vstd::prelude::*;

use super::{
    addr::{PAddr, VAddr, VIdx, WORD_SIZE},
    frame::Frame,
    hardware::HardwareState,
    high_level::{HighLevelConstants, HighLevelState},
    op::{MapOp, QueryOp, ReadOp, TLBEvictOp, TLBFillOp, UnmapOp, WriteOp},
    pt_spec::{PTConstants, PageTableState},
    s1pt::S1PageTable,
};

verus! {

/// Low-level Memory State, which includes
///
/// - Common memory: Memory used by the OS and applications.
/// - Page table: Stage 1 page table.
/// - TLB: Translation Lookaside Buffer.
pub struct LowLevelState {
    /// 8-byte-indexed physical memory.
    pub mem: Seq<nat>,
    /// Page table.
    pub pt: S1PageTable,
    /// Translation Lookaside Buffer.
    pub tlb: Map<VAddr, Frame>,
}

/// State transition specification.
impl LowLevelState {
    /// Initial memory state.
    ///
    /// The initial state must satisfy the specification.
    pub open spec fn init(self) -> bool {
        HardwareState::init(self.hw_state())
    }

    /// State transition - Memory read.
    pub open spec fn read(s1: Self, s2: Self, op: ReadOp) -> bool {
        HardwareState::read(s1.hw_state(), s2.hw_state(), op)
    }

    /// State transition - Memory write.
    pub open spec fn write(s1: Self, s2: Self, op: WriteOp) -> bool {
        HardwareState::write(s1.hw_state(), s2.hw_state(), op)
    }

    /// State transition - Map a frame.
    pub open spec fn map(s1: Self, s2: Self, op: MapOp) -> bool {
        // Page table spec satisfied
        &&& PageTableState::map(
            s1.pt_state(),
            s2.pt_state(),
            op,
        )
        // Hardware behaves as spec
        &&& HardwareState::pt_op(s1.hw_state(), s2.hw_state())
    }

    /// State transition - Unmap a frame.
    pub open spec fn unmap(s1: Self, s2: Self, op: UnmapOp) -> bool {
        // Page table spec satisfied
        &&& PageTableState::unmap(
            s1.pt_state(),
            s2.pt_state(),
            op,
        )
        // Hardware behaves as spec
        &&& HardwareState::pt_op(
            s1.hw_state(),
            s2.hw_state(),
        )
        // Hardware ensures TLB doesn't contain the unmapped frame
        &&& !s2.tlb.contains_key(op.vaddr)
    }

    /// State transition - Query a vaddr.
    pub open spec fn query(s1: Self, s2: Self, op: QueryOp) -> bool {
        // Page table spec satisfied
        &&& PageTableState::query(
            s1.pt_state(),
            s2.pt_state(),
            op,
        )
        // Hardware behaves as spec
        &&& HardwareState::pt_op(s1.hw_state(), s2.hw_state())
    }

    /// State transition - TLB fill.
    pub open spec fn tlb_fill(s1: Self, s2: Self, op: TLBFillOp) -> bool {
        // Hardware behaves as spec
        HardwareState::tlb_fill(s1.hw_state(), s2.hw_state(), op)
    }

    /// State transition - TLB evict.
    pub open spec fn tlb_evict(s1: Self, s2: Self, op: TLBEvictOp) -> bool {
        // Hardware behaves as spec
        HardwareState::tlb_evict(s1.hw_state(), s2.hw_state(), op)
    }
}

/// State Invariants.
impl LowLevelState {
    /// All frames are within the physical memory bounds.
    pub open spec fn frames_within_pmem(self) -> bool {
        forall|base: VAddr, frame: Frame| #[trigger]
            self.pt.interpret().contains_pair(base, frame) ==> frame.base.0 + frame.size.as_nat()
                <= self.mem.len()
    }

    /// All mappings (vbase, pbase) are 8-byte aligned.
    pub open spec fn mappings_aligned(self) -> bool {
        forall|base: VAddr, frame: Frame| #[trigger]
            self.pt.interpret().contains_pair(base, frame) ==> base.aligned(WORD_SIZE)
                && frame.base.aligned(WORD_SIZE)
    }

    /// Page table mappings do not overlap in virtual memory.
    pub open spec fn mappings_nonoverlap_in_vmem(self) -> bool {
        forall|base1: VAddr, frame1: Frame, base2: VAddr, frame2: Frame|
            self.pt.interpret().contains_pair(base1, frame1) && self.pt.interpret().contains_pair(
                base2,
                frame2,
            ) ==> ((base1 == base2) || !VAddr::overlap(
                base1,
                frame1.size.as_nat(),
                base2,
                frame2.size.as_nat(),
            ))
    }

    /// Page table mappings do not overlap in physical memory.
    pub open spec fn mappings_nonoverlap_in_pmem(self) -> bool {
        forall|base1: VAddr, frame1: Frame, base2: VAddr, frame2: Frame|
            self.pt.interpret().contains_pair(base1, frame1) && self.pt.interpret().contains_pair(
                base2,
                frame2,
            ) ==> ((base1 == base2) || !PAddr::overlap(
                frame1.base,
                frame1.size.as_nat(),
                frame2.base,
                frame2.size.as_nat(),
            ))
    }

    /// TLB must be a submap of the page table.
    pub open spec fn tlb_is_submap_of_pt(self) -> bool {
        forall|base, frame|
            self.tlb.contains_pair(base, frame) ==> #[trigger] self.pt.interpret().contains_pair(
                base,
                frame,
            )
    }

    /// OS state invariants.
    pub open spec fn invariants(self) -> bool {
        &&& self.frames_within_pmem()
        &&& self.mappings_aligned()
        &&& self.mappings_nonoverlap_in_vmem()
        &&& self.mappings_nonoverlap_in_pmem()
        &&& self.tlb_is_submap_of_pt()
    }
}

/// View(abstraction) functions. `LowLevelState` --Abstratcion--> `HighLevelState`
impl LowLevelState {
    /// Collect all page mappings managed by OS memory state (pt_mem and TLB).
    pub open spec fn all_mappings(self) -> Map<VAddr, Frame> {
        Map::new(
            |base: VAddr| self.tlb.contains_key(base) || self.pt.interpret().contains_key(base),
            |base: VAddr|
                {
                    if self.tlb.contains_key(base) {
                        self.tlb[base]
                    } else {
                        self.pt.interpret()[base]
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
    pub open spec fn view(self) -> HighLevelState {
        HighLevelState {
            mem: self.interpret_mem(),
            mappings: self.all_mappings(),
            constants: HighLevelConstants { pmem_size: self.mem.len() },
        }
    }
}

/// Helper functions.
impl LowLevelState {
    /// If exists a mapping that `vaddr` lies in.
    pub open spec fn has_mapping_for(self, vaddr: VAddr) -> bool {
        exists|base: VAddr, frame: Frame| #[trigger]
            self.pt.interpret().contains_pair(base, frame) && vaddr.within(
                base,
                frame.size.as_nat(),
            )
    }

    /// Extract the state that hardware should consider.
    pub open spec fn hw_state(self) -> HardwareState {
        HardwareState { mem: self.mem, pt: self.pt, tlb: self.tlb }
    }

    /// Extract the state that page table implementation should consider.
    pub open spec fn pt_state(self) -> PageTableState {
        PageTableState {
            mappings: self.pt.interpret(),
            constants: PTConstants { pmem_size: self.mem.len() },
        }
    }
}

} // verus!
