//! Prove that OS state machine refines the high-level state machine.
use super::lemmas::*;
use crate::spec::{
    hl::HlMemoryState,
    mem::{ReadOp, WriteOp},
    os::OSMemoryState,
};
use vstd::prelude::*;

verus! {

/// Lemma. If the TLB is a subset of the page table, then the interpreted page table
/// memory is equal to the all mappings (page table & TLB).
proof fn lemma_interpret_pt_mem_equals_all_mappings(st: OSMemoryState)
    requires
        st.tlb_is_submap_of_pt(),
    ensures
        st.interpret_pt_mem() === st.all_mappings(),
{
    let pt_mem = st.interpret_pt_mem();
    let tlb = st.tlb;
    let all_mappings = st.all_mappings();

    // 1. Any mapping in `all_mappings` is also in `pt_mem`.
    assert(forall|addr, frame| #[trigger]
        all_mappings.contains_pair(addr, frame) ==> pt_mem.contains_pair(addr, frame));

    // 2. Any mapping in `pt_mem` is also in `all_mappings`.
    assert forall|addr, frame| #[trigger]
        pt_mem.contains_pair(addr, frame) implies all_mappings.contains_pair(addr, frame) by {
        if tlb.contains_key(addr) {
            assert(all_mappings.contains_pair(addr, tlb[addr]));
        } else {
            assert(all_mappings.contains_pair(addr, pt_mem[addr]));
        }
    }

    // 3. The two maps are equal.
    lemma_map_eq_pair(pt_mem, all_mappings);
}

/// Theorem. The OS-level init state refines the high-level init state.
proof fn os_init_refines_hl_init(st: OSMemoryState)
    requires
        st.tlb_is_submap_of_pt(),
        st.init(),
    ensures
        st@.init(),
{
    // 1. The interpreted mappings are empty if page table and TLB are empty.
    lemma_interpret_pt_mem_equals_all_mappings(st);
    assert(st@.mappings =~= Map::empty());

    // 2. Empty mappings result in empty memory.
    assert(st.interpret_mem() === Map::empty());
}

/// Theorem. The OS-level read operation refines the high-level read operation.
proof fn os_read_refines_hl_read(s1: OSMemoryState, s2: OSMemoryState, op: ReadOp)
    requires
        OSMemoryState::mem_read(s1, s2, op),
    ensures
        HlMemoryState::read(s1@, s2@, op),
{
    // TODO
    assume(HlMemoryState::read(s1@, s2@, op));
}

/// Theorem: The OS-level write operation refines the high-level write operation.
proof fn os_write_refines_hl_write(s1: OSMemoryState, s2: OSMemoryState, op: WriteOp)
    requires
        OSMemoryState::mem_write(s1, s2, op),
    ensures
        HlMemoryState::write(s1@, s2@, op),
{
    // TODO
    assume(HlMemoryState::write(s1@, s2@, op));
}

} // verus!
