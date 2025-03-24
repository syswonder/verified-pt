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
    addr::{PAddr, VAddr, VIdx},
    frame::Frame,
    hardware::{HardwareState, PhysMem, TLB},
    high_level::{HighLevelConstants, HighLevelState},
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
    /// Physical memory.
    pub mem: PhysMem,
    /// Page table.
    pub pt: S1PageTable,
    /// Translation Lookaside Buffer.
    pub tlb: TLB,
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
    pub open spec fn read(s1: Self, s2: Self, vaddr: VAddr, res: Result<u64, ()>) -> bool {
        HardwareState::read(s1.hw_state(), s2.hw_state(), vaddr, res)
    }

    /// State transition - Memory write.
    pub open spec fn write(
        s1: Self,
        s2: Self,
        vaddr: VAddr,
        value: u64,
        res: Result<(), ()>,
    ) -> bool {
        HardwareState::write(s1.hw_state(), s2.hw_state(), vaddr, value, res)
    }

    /// State transition - Explicit TLB eviction.
    ///
    /// Hypervisor uses specific instructions to evict TLB entries explicitly.
    pub open spec fn tlb_evict(s1: Self, s2: Self, base: VAddr) -> bool {
        HardwareState::tlb_evict(s1.hw_state(), s2.hw_state(), base)
    }

    /// State transition - Map a frame.
    pub open spec fn map(
        s1: Self,
        s2: Self,
        base: VAddr,
        frame: Frame,
        res: Result<(), ()>,
    ) -> bool {
        // Page table spec satisfied
        &&& PageTableState::map(
            s1.pt_state(),
            s2.pt_state(),
            base,
            frame,
            res,
        )
        // Hardware behaves as spec
        &&& HardwareState::pt_op(s1.hw_state(), s2.hw_state())
    }

    /// State transition - Unmap a frame.
    pub open spec fn unmap(s1: Self, s2: Self, base: VAddr, res: Result<(), ()>) -> bool {
        // Page table spec satisfied
        &&& PageTableState::unmap(
            s1.pt_state(),
            s2.pt_state(),
            base,
            res,
        )
        // Hardware behaves as spec
        &&& HardwareState::pt_op(
            s1.hw_state(),
            s2.hw_state(),
        )
        // TLB doesn't contain the unmapped frame
        // Normally, hypervisor ensures this using specific instructions.
        &&& !s2.tlb.contains_base(base)
    }

    /// State transition - Query a vaddr.
    pub open spec fn query(
        s1: Self,
        s2: Self,
        vaddr: VAddr,
        res: Result<(VAddr, Frame), ()>,
    ) -> bool {
        // Page table spec satisfied
        &&& PageTableState::query(
            s1.pt_state(),
            s2.pt_state(),
            vaddr,
            res,
        )
        // Hardware behaves as spec
        &&& HardwareState::pt_op(s1.hw_state(), s2.hw_state())
    }
}

/// State Invariants.
impl LowLevelState {
    /// All frames are within the physical memory bounds.
    pub open spec fn frames_within_pmem(self) -> bool {
        forall|base: VAddr, frame: Frame| #[trigger]
            self.pt.interpret().contains_pair(base, frame) ==> self.mem.contains(frame.base.idx())
                && self.mem.contains(frame.base.offset(frame.size.as_nat()).idx())
    }

    /// All mappings (vbase, pbase) are 8-byte aligned.
    pub open spec fn mappings_aligned(self) -> bool {
        forall|base: VAddr, frame: Frame| #[trigger]
            self.pt.interpret().contains_pair(base, frame) ==> base.aligned(frame.size.as_nat())
                && frame.base.aligned(frame.size.as_nat())
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
            self.tlb.contains_mapping(base, frame) ==> #[trigger] self.pt.interpret().contains_pair(
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
            |base: VAddr| self.tlb.contains_base(base) || self.pt.interpret().contains_key(base),
            |base: VAddr|
                {
                    if self.tlb.contains_base(base) {
                        self.tlb.index(base)
                    } else {
                        self.pt.interpret()[base]
                    }
                },
        )
    }

    /// Interpret the common memory as a map (vidx -> word value).
    pub open spec fn interpret_mem(self) -> Map<VIdx, u64> {
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
                    self.mem.read(vidx.addr().map(base, frame.base).idx())
                },
        )
    }

    /// High-level (abstract) view of the OS memory state.
    pub open spec fn view(self) -> HighLevelState {
        HighLevelState {
            mem: self.interpret_mem(),
            mappings: self.all_mappings(),
            constants: HighLevelConstants { pmem_lb: self.mem.lb(), pmem_ub: self.mem.ub() },
        }
    }
}

/// Helper functions.
impl LowLevelState {
    /// If exists a mapping that `vaddr` lies in.
    pub open spec fn has_mapping_for(self, vaddr: VAddr) -> bool {
        exists|base: VAddr, frame: Frame| #[trigger]
            self.all_mappings().contains_pair(base, frame) && vaddr.within(
                base,
                frame.size.as_nat(),
            )
    }

    /// Get the mapping that `vaddr` lies in.
    pub open spec fn mapping_for(self, vaddr: VAddr) -> (VAddr, Frame)
        recommends
            self.has_mapping_for(vaddr),
    {
        choose|base: VAddr, frame: Frame| #[trigger]
            self.all_mappings().contains_pair(base, frame) && vaddr.within(
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
            constants: PTConstants { pmem_ub: self.mem.ub(), pmem_lb: self.mem.lb() },
        }
    }
}

} // verus!
