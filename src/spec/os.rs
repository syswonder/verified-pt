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
use super::{
    hl::HlMemoryState,
    mem::{Frame, PageTableMem},
    nat_to_u64,
    s1pt::page_table_walk,
    PAddr, VAddr, VWordIdx,
};
use vstd::prelude::*;

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
    /// Word-indexed physical memory.
    pub mem: Seq<nat>,
    /// Page table memory.
    pub pt_mem: PageTableMem,
    /// TLB.
    pub tlb: Map<VAddr, Frame>,
}

impl OSMemoryState {
    /// If there is a mapped virtual page that `vaddr` lies in.
    pub open spec fn exists_mapping_for(self, vaddr: VAddr) -> bool {
        exists|base: VAddr, frame: Frame| #[trigger]
            self.interpret_pt_mem().contains_pair(base, frame) && vaddr.within(
                base,
                frame.size.as_nat(),
            )
    }

    /// Interpret the page table memory as a map (vaddr -> frame).
    pub open spec fn interpret_pt_mem(self) -> Map<VAddr, Frame> {
        let max_base: nat = 0x8000_0000;
        Map::new(
            |addr: VAddr|
                addr.0 < max_base && exists|frame: Frame| #[trigger]
                    page_table_walk(self.pt_mem, nat_to_u64(addr.0), frame),
            |addr: VAddr|
                choose|pte: Frame| #[trigger] page_table_walk(self.pt_mem, nat_to_u64(addr.0), pte),
        )
    }

    /// Interpret the common memory as a map (vword_idx -> word value).
    pub open spec fn interpret_mem(self) -> Map<VWordIdx, nat> {
        Map::new(
            |vword_idx: VWordIdx|
                exists|base: VAddr, frame: Frame|
                    {
                        &&& #[trigger] self.all_mappings().contains_pair(base, frame)
                        &&& vword_idx.addr().within(base, frame.size.as_nat())
                    },
            |vword_idx: VWordIdx|
                {
                    let (base, frame) = choose|base: VAddr, frame: Frame|
                        {
                            &&& #[trigger] self.all_mappings().contains_pair(base, frame)
                            &&& vword_idx.addr().within(base, frame.size.as_nat())
                        };
                    self.mem.index(vword_idx.addr().map(base, frame.base).word_idx().as_int())
                },
        )
    }

    /// Collect all page mappings managed by OS memory state (pt_mem and TLB).
    pub open spec fn all_mappings(self) -> Map<VAddr, Frame> {
        Map::new(
            |base: VAddr| self.tlb.contains_key(base) || self.interpret_pt_mem().contains_key(base),
            |base: VAddr|
                {
                    if self.tlb.contains_key(base) {
                        self.tlb.index(base)
                    } else {
                        self.interpret_pt_mem().index(base)
                    }
                },
        )
    }

    /// High-level (abstract) view of the OS memory state.
    pub open spec fn view(self) -> HlMemoryState {
        HlMemoryState { mem: self.interpret_mem(), mappings: self.all_mappings() }
    }

    /* Invariants */
    /// Page table mappings do not overlap in virtual memory.
    pub open spec fn pt_mappings_nonoverlap_in_vmem(self) -> bool {
        forall|base1: VAddr, frame1: Frame, base2: VAddr, frame2: Frame|
            self.interpret_pt_mem().contains_pair(base1, frame1)
                && self.interpret_pt_mem().contains_pair(base2, frame2) ==> ((base1 == base2)
                || !VAddr::overlap(base1, frame1.size.as_nat(), base2, frame2.size.as_nat()))
    }

    /// Page table mappings do not overlap in physical memory.
    pub open spec fn pt_mappings_nonoverlap_in_pmem(self) -> bool {
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
        &&& self.interpret_pt_mem() === Map::empty()
    }
}

} // verus!
