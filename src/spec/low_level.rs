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
    arch::PTArch,
    frame::Frame,
    hardware::{HardwareState, PhysMem, TLB},
    high_level::{HighLevelConstants, HighLevelState},
    pt_mem::PageTableMem,
    pt_spec::{PTConstants, PageTableState},
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
    pub pt: PageTableMem,
    /// Translation Lookaside Buffer.
    pub tlb: TLB,
    /// Constants.
    pub constants: LowLevelConstants,
}

/// Constants for the low-level state.
pub struct LowLevelConstants {
    /// Page table architecture
    pub arch: PTArch,
}

/// State transition specification.
impl LowLevelState {
    /// Initial memory state.
    ///
    /// The initial state must satisfy the specification.
    pub open spec fn init(self) -> bool {
        &&& self.constants.arch.valid()
        &&& HardwareState::init(self.hw_state())
    }

    /// State transition - Memory read.
    pub open spec fn read(s1: Self, s2: Self, vaddr: VAddr, res: Result<u64, ()>) -> bool {
        &&& s1.constants === s2.constants
        &&& HardwareState::read(s1.hw_state(), s2.hw_state(), vaddr, res)
    }

    /// State transition - Memory write.
    pub open spec fn write(
        s1: Self,
        s2: Self,
        vaddr: VAddr,
        value: u64,
        res: Result<(), ()>,
    ) -> bool {
        &&& s1.constants === s2.constants
        &&& HardwareState::write(s1.hw_state(), s2.hw_state(), vaddr, value, res)
    }

    /// State transition - Explicit TLB eviction.
    ///
    /// Hypervisor uses specific instructions to evict TLB entries explicitly.
    pub open spec fn tlb_evict(s1: Self, s2: Self, vbase: VAddr) -> bool {
        &&& s1.constants === s2.constants
        &&& HardwareState::tlb_evict(s1.hw_state(), s2.hw_state(), vbase)
    }

    /// State transition - Map a frame.
    pub open spec fn map(
        s1: Self,
        s2: Self,
        vbase: VAddr,
        frame: Frame,
        res: Result<(), ()>,
    ) -> bool {
        &&& s1.constants === s2.constants
        // Page table spec satisfied
        &&& PageTableState::map(
            s1.pt_state(),
            s2.pt_state(),
            vbase,
            frame,
            res,
        )
        // Hardware behaves as spec
        &&& HardwareState::pt_op(s1.hw_state(), s2.hw_state())
    }

    /// State transition - Unmap a frame.
    pub open spec fn unmap(s1: Self, s2: Self, vbase: VAddr, res: Result<(), ()>) -> bool {
        &&& s1.constants === s2.constants
        // Page table spec satisfied
        &&& PageTableState::unmap(
            s1.pt_state(),
            s2.pt_state(),
            vbase,
            res,
        )
        // Hardware behaves as spec
        &&& HardwareState::pt_op(
            s1.hw_state(),
            s2.hw_state(),
        )
        // TLB doesn't contain the unmapped frame
        // Normally, hypervisor ensures this using specific instructions.
        &&& !s2.tlb.contains_base(vbase)
    }

    /// State transition - Query a vaddr.
    pub open spec fn query(
        s1: Self,
        s2: Self,
        vaddr: VAddr,
        res: Result<(VAddr, Frame), ()>,
    ) -> bool {
        &&& s1.constants === s2.constants
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
        forall|vbase: VAddr, frame: Frame| #[trigger]
            self.pt.interpret().contains_pair(vbase, frame) ==> self.mem.lb().0
                <= frame.base.idx().0 && frame.base.offset(frame.size.as_nat()).idx().0
                <= self.mem.ub().0
    }

    /// All mappings (vbase, pbase) are 8-byte aligned.
    pub open spec fn mappings_aligned(self) -> bool {
        forall|vbase: VAddr, frame: Frame| #[trigger]
            self.pt.interpret().contains_pair(vbase, frame) ==> vbase.aligned(frame.size.as_nat())
                && frame.base.aligned(frame.size.as_nat())
    }

    /// Page table mappings do not overlap in virtual memory.
    pub open spec fn mappings_nonoverlap_in_vmem(self) -> bool {
        forall|vbase1: VAddr, frame1: Frame, vbase2: VAddr, frame2: Frame|
            self.pt.interpret().contains_pair(vbase1, frame1) && self.pt.interpret().contains_pair(
                vbase2,
                frame2,
            ) ==> vbase1 == vbase2 || !VAddr::overlap(
                vbase1,
                frame1.size.as_nat(),
                vbase2,
                frame2.size.as_nat(),
            )
    }

    /// Page table mappings do not overlap in physical memory.
    pub open spec fn mappings_nonoverlap_in_pmem(self) -> bool {
        forall|vbase1: VAddr, frame1: Frame, vbase2: VAddr, frame2: Frame|
            self.pt.interpret().contains_pair(vbase1, frame1) && self.pt.interpret().contains_pair(
                vbase2,
                frame2,
            ) ==> vbase1 == vbase2 || !PAddr::overlap(
                frame1.base,
                frame1.size.as_nat(),
                frame2.base,
                frame2.size.as_nat(),
            )
    }

    /// TLB must be a submap of the page table.
    pub open spec fn tlb_is_submap_of_pt(self) -> bool {
        forall|vbase, frame|
            self.tlb.contains_mapping(vbase, frame)
                ==> #[trigger] self.pt.interpret().contains_pair(vbase, frame)
    }

    /// OS state invariants.
    pub open spec fn invariants(self) -> bool {
        &&& self.constants.arch.valid()
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
            |vbase: VAddr| self.tlb.contains_base(vbase) || self.pt.interpret().contains_key(vbase),
            |vbase: VAddr|
                {
                    if self.tlb.contains_base(vbase) {
                        self.tlb.index(vbase)
                    } else {
                        self.pt.interpret()[vbase]
                    }
                },
        )
    }

    /// Interpret the common memory as a map (vidx -> word value).
    pub open spec fn interpret_mem(self) -> Map<VIdx, u64> {
        Map::new(
            |vidx: VIdx|
                exists|vbase: VAddr, frame: Frame|
                    {
                        &&& #[trigger] self.all_mappings().contains_pair(vbase, frame)
                        &&& vidx.addr().within(vbase, frame.size.as_nat())
                    },
            |vidx: VIdx|
                {
                    let (vbase, frame) = choose|vbase: VAddr, frame: Frame|
                        {
                            &&& #[trigger] self.all_mappings().contains_pair(vbase, frame)
                            &&& vidx.addr().within(vbase, frame.size.as_nat())
                        };
                    self.mem.read(vidx.addr().map(vbase, frame.base).idx())
                },
        )
    }

    /// High-level (abstract) view of the OS memory state.
    pub open spec fn view(self) -> HighLevelState {
        HighLevelState {
            mem: self.interpret_mem(),
            mappings: self.all_mappings(),
            constants: HighLevelConstants {
                arch: self.constants.arch,
                pmem_lb: self.mem.lb(),
                pmem_ub: self.mem.ub(),
            },
        }
    }
}

/// Helper functions.
impl LowLevelState {
    /// If exists a mapping that `vaddr` lies in.
    pub open spec fn has_mapping_for(self, vaddr: VAddr) -> bool {
        exists|vbase: VAddr, frame: Frame| #[trigger]
            self.all_mappings().contains_pair(vbase, frame) && vaddr.within(
                vbase,
                frame.size.as_nat(),
            )
    }

    /// Get the mapping that `vaddr` lies in.
    pub open spec fn mapping_for(self, vaddr: VAddr) -> (VAddr, Frame)
        recommends
            self.has_mapping_for(vaddr),
    {
        choose|vbase: VAddr, frame: Frame| #[trigger]
            self.all_mappings().contains_pair(vbase, frame) && vaddr.within(
                vbase,
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
            constants: PTConstants {
                arch: self.constants.arch,
                pmem_ub: self.mem.ub().addr(),
                pmem_lb: self.mem.lb().addr(),
            },
        }
    }
}

} // verus!
