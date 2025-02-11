//! Hardware abstract state and state machine.

use vstd::prelude::*;

use super::{
    mem::{Frame, PageTableMem},
    s1pt::page_table_walk,
};

verus! {

/// Abstract hardware memory state, including
///
/// - Common memory: Memory used by the OS and applications.
/// - Page table memory: Memory used to store page tables.
/// - TLB: Translation Lookaside Buffer.
pub struct HardwareState {
    /// Common memory.
    mem: Seq<nat>,
    /// Page table memory.
    pt_mem: PageTableMem,
    /// TLB.
    tlb: Map<nat, Frame>
}

impl HardwareState {
    /* State transition specifications */

    /// Initial state.
    /// 
    /// The initial state must satisfy the specification.
    pub open spec fn init() -> bool {
        // TODO
        true
    }

    /// State transition - Common memory read & write operation.
    ///
    /// The pre-state `s1` and post-state `s2` must satisfy the specification
    /// after common memory read & write operation.
    pub open spec fn mem_read_write(s1: Self, s2: Self, vaddr: nat, paddr: nat, write: bool) -> bool {
        // TODO
        true
    }

    /// State transition - Page table memory operation.
    ///
    /// The pre-state `s1` and post-state `s2` must satisfy the specification
    /// after page table memory operation.
    pub open spec fn pt_mem_op(s1: Self, s2: Self) -> bool {
        // TODO
        true
    }

    /// State transition - TLB fill operation.
    ///
    /// The pre-state `s1` and post-state `s2` must satisfy the specification
    /// after TLB fill operation.
    pub open spec fn tlb_fill(s1: Self, s2: Self, vaddr: nat, frame: Frame) -> bool {
        // TODO
        true
    }

    /// State transition - TLB eviction operation.
    ///
    /// The pre-state `s1` and post-state `s2` must satisfy the specification
    /// after TLB eviction operation.
    pub open spec fn tlb_evict(s1: Self, s2: Self, vaddr: nat) -> bool {
        // TODO
        true
    }
}

pub spec const MAX_BASE: nat = 0x8000_0000;

/// Serialize the page table memory to a page map.
pub open spec fn serialize_pt_mem(pt_mem: PageTableMem) -> Map<nat, Frame> {
    Map::new(
        |addr: nat|
            addr < MAX_BASE && exists|frame: Frame| #[trigger] page_table_walk(pt_mem, addr as u64, frame),
        |addr: nat| choose|pte: Frame| #[trigger] page_table_walk(pt_mem, addr as u64, pte),
    )
}

} // verus!
