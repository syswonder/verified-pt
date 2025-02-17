//! OS-level memory state transtition specification.
//!
//! OS level is the highest level of memory state transition specification, which describes
//! how the whole memory system behaves.
//!
//! OS state transition step includes
//!
//! - Hardware-level operations
//! - page table map & unmap
//! - ...

use vstd::prelude::*;
use super::overlap;
use super::mem::{PageTableMem, Frame, interpret_pt_mem};

verus! {

/// OS-level Memory State, which includes
///
/// - Common memory: Memory used by the OS and applications.
/// - Page table memory: Memory used to store page tables.
/// - TLB: Translation Lookaside Buffer.
///
/// OS-level memory state is the operand of the OS memory state machine. The memory state
/// machine specifies the behavior of the memory management unit. These specifications are
/// composed of the following parts:
///
/// - Hardware. This level specifies the behavior of the memory management unit.
///   The hardware behavior must be a refinement of the specification.
///
/// - Page table. Describing the page table functions’ behavior as a state machine
///   operating on an abstract view of the page table.
///
/// - OS. The highest level of memory state transition specification, which integrates
///   the hardware level and the page table level, and describeschow the whole memory
///   system behaves.
///
/// Specifications are defined in corresponding modules.
pub struct OSMemoryState {
    /// Common memory.
    pub mem: Seq<nat>,
    /// Page table memory.
    pub pt_mem: PageTableMem,
    /// TLB.
    pub tlb: Map<nat, Frame>,
}

impl OSMemoryState {
    /// Interpret the page table memory as a map.
    pub open spec fn interpret_pt_mem(self) -> Map<nat, Frame> {
        interpret_pt_mem(self.pt_mem)
    }

    /* Invariants */

    /// Page table mappings do not overlap in virtual memory.
    pub open spec fn pt_mappings_nonoverlap_in_vmem(self) -> bool {
        forall|base1: nat, frame1: Frame, base2: nat, frame2: Frame|
            self.interpret_pt_mem().contains_pair(base1, frame1)
                && self.interpret_pt_mem().contains_pair(base2, frame2) ==> ((base1 == base2)
                || !overlap(base1, frame1.size.to_nat(), base2, frame2.size.to_nat()))
    }

    /// Page table mappings do not overlap in physical memory.
    pub open spec fn pt_mappings_nonoverlap_in_pmem(self) -> bool {
        forall|base1: nat, frame1: Frame, base2: nat, frame2: Frame|
            self.interpret_pt_mem().contains_pair(base1, frame1)
                && self.interpret_pt_mem().contains_pair(base2, frame2) ==> ((base1 == base2)
                || !overlap(base1, frame1.size.to_nat(), base2, frame2.size.to_nat()))
    }

    /// TLB must be a submap of the page table.
    pub open spec fn tlb_is_submap_of_pt(self) -> bool {
        forall|base, frame|
            self.tlb.contains_pair(base, frame)
                ==> #[trigger] self.interpret_pt_mem().contains_pair(base, frame)
    }

    /// OS state invariants.
    pub open spec fn invariants(self) -> bool {
        &&& self.pt_mappings_nonoverlap_in_vmem()
        &&& self.pt_mappings_nonoverlap_in_pmem()
        &&& self.tlb_is_submap_of_pt()
    }

    /* State transition */

    /// Initial memory state.
    ///
    /// The initial state must satisfy the specification.
    pub open spec fn init(self) -> bool {
        &&& self.tlb.dom() === Set::empty()
        &&& interpret_pt_mem(self.pt_mem) === Map::empty()
    }
}

} // verus!
