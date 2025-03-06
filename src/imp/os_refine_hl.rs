//! Prove that OS state machine refines the high-level state machine.
use super::lemmas::*;
use crate::spec::{
    addr::VAddr,
    hl::HlMemoryState,
    mem::{Frame, ReadOp, WriteOp, MapOp, UnmapOp},
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

/// Lemma. If there is no overlap in the virtual memory space, then there is at most
/// one mapping containing a virtual address.
proof fn lemma_at_most_one_mapping_for_vaddr(st: OSMemoryState, vaddr: VAddr)
    requires
        st.mappings_nonoverlap_in_vmem(),
    ensures
        forall|base1, frame1, base2, frame2|
            {
                &&& #[trigger] st.interpret_pt_mem().contains_pair(base1, frame1)
                &&& vaddr.within(base1, frame1.size.as_nat())
                &&& #[trigger] st.interpret_pt_mem().contains_pair(base2, frame2)
                &&& vaddr.within(base2, frame2.size.as_nat())
            } ==> base1 == base2,
{
    if exists|base1, frame1, base2, frame2|
        {
            &&& #[trigger] st.interpret_pt_mem().contains_pair(base1, frame1)
            &&& vaddr.within(base1, frame1.size.as_nat())
            &&& #[trigger] st.interpret_pt_mem().contains_pair(base2, frame2)
            &&& vaddr.within(base2, frame2.size.as_nat())
            &&& base1 != base2
        } {
        // Proof by contradiction. If there are two mappings for `vaddr`,
        // then there is an overlap.
        let (base1, frame1, base2, frame2): (VAddr, Frame, VAddr, Frame) = choose|
            base1,
            frame1,
            base2,
            frame2,
        |
            {
                &&& #[trigger] st.interpret_pt_mem().contains_pair(base1, frame1)
                &&& vaddr.within(base1, frame1.size.as_nat())
                &&& #[trigger] st.interpret_pt_mem().contains_pair(base2, frame2)
                &&& vaddr.within(base2, frame2.size.as_nat())
                &&& base1 != base2
            };
        assert(VAddr::overlap(base1, frame1.size.as_nat(), base2, frame2.size.as_nat()));
    }
}

/// Lemma. If there is no overlap in the physical memory space, then 2 different virtual
/// addresses cannot map to the same physical address.
proof fn lemma_different_paddrs_for_different_vaddrs(
    st: OSMemoryState,
    vaddr1: VAddr,
    vaddr2: VAddr,
)
    requires
        st.mappings_nonoverlap_in_pmem(),
        vaddr1 != vaddr2,
    ensures
        forall|base1: VAddr, frame1: Frame, base2: VAddr, frame2: Frame|
            {
                &&& #[trigger] st.interpret_pt_mem().contains_pair(base1, frame1)
                &&& #[trigger] vaddr1.within(base1, frame1.size.as_nat())
                &&& #[trigger] st.interpret_pt_mem().contains_pair(base2, frame2)
                &&& #[trigger] vaddr2.within(base2, frame2.size.as_nat())
            } ==> vaddr1.map(base1, frame1.base) != vaddr2.map(base2, frame2.base),
{
}

/// Theorem. The OS-level init state implies the invariants.
proof fn os_init_implies_invariants(st: OSMemoryState)
    requires
        st.init(),
    ensures
        st.invariants(),
{
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
    assert(st@.mappings === Map::empty());
    // 2. Empty mappings result in empty memory.
    assert(st.interpret_mem() === Map::empty());
}

/// Theorem. The OS-level read operation preserves the invariants.
proof fn os_read_preserves_invariants(s1: OSMemoryState, s2: OSMemoryState, op: ReadOp)
    requires
        s1.invariants(),
        OSMemoryState::read(s1, s2, op),
    ensures
        s2.invariants(),
{
}

/// Theorem. The OS-level read operation refines the high-level read operation.
proof fn os_read_refines_hl_read(s1: OSMemoryState, s2: OSMemoryState, op: ReadOp)
    requires
        s1.invariants(),
        OSMemoryState::read(s1, s2, op),
    ensures
        HlMemoryState::read(s1@, s2@, op),
{
    // Lemmas satisfied by the invariants.
    lemma_interpret_pt_mem_equals_all_mappings(s1);
    lemma_at_most_one_mapping_for_vaddr(s1, op.vaddr);

    match op.mapping {
        Some((base, frame)) => {
            let pidx = op.vaddr.map(base, frame.base).idx();
            if pidx.0 < s1.mem.len() && frame.attr.readable && frame.attr.user_accessible {
                // `s1` has the mapping `(base, frame)` which contains `op.vaddr`.
                assert(s1.all_mappings().contains_pair(base, frame));
                assert(op.vaddr.within(base, frame.size.as_nat()));
                // Values in the intepreted memory are the same as in the OS memory, because
                // there is only one mapping for `op.vaddr` (lemma).
                assert(s1.interpret_mem()[op.vaddr.idx()] === s1.mem[pidx.as_int()]);
            }
        },
        None => {
            // Satisfied because interpret_pt_mem equals all_mappings (lemma).
            assert(!s1@.mem_domain_covered_by_mappings().contains(op.vaddr.idx()));
        },
    }
}

/// Theorem. The OS-level write operation preserves the invariants.
proof fn os_write_preserves_invariants(s1: OSMemoryState, s2: OSMemoryState, op: WriteOp)
    requires
        s1.invariants(),
        OSMemoryState::write(s1, s2, op),
    ensures
        s2.invariants(),
{
    assert(s1.interpret_pt_mem() === s2.interpret_pt_mem());
}

/// Theorem: The OS-level write operation refines the high-level write operation.
proof fn os_write_refines_hl_write(s1: OSMemoryState, s2: OSMemoryState, op: WriteOp)
    requires
        s1.invariants(),
        OSMemoryState::write(s1, s2, op),
    ensures
        HlMemoryState::write(s1@, s2@, op),
{
    // Lemmas satisfied by the invariants.
    lemma_interpret_pt_mem_equals_all_mappings(s1);
    lemma_at_most_one_mapping_for_vaddr(s2, op.vaddr);

    match op.mapping {
        Some((base, frame)) => {
            let pidx = op.vaddr.map(base, frame.base).idx();
            if pidx.0 < s1.mem.len() && frame.attr.writable && frame.attr.user_accessible {
                // `s1` has the mapping `(base, frame)` which contains `op.vaddr`.
                assert(s1.all_mappings().contains_pair(base, frame));
                assert(op.vaddr.within(base, frame.size.as_nat()));
                // Value updated in the physical memory is the same as in the interpreted memory,
                // because there is only one mapping for `op.vaddr` (lemma).
                assert(s2.interpret_mem() === s1.interpret_mem().insert(
                    op.vaddr.idx(),
                    op.value,
                ));
            }
        },
        None => {
            // Satisfied because interpret_pt_mem equals all_mappings (lemma).
            assert(!s1@.mem_domain_covered_by_mappings().contains(op.vaddr.idx()));
        },
    }
}

/// Theorem. The OS-level map operation preserves the invariants.
proof fn os_map_preserves_invariants(s1: OSMemoryState, s2: OSMemoryState, op: MapOp)
    requires
        s1.invariants(),
        OSMemoryState::map(s1, s2, op),
    ensures
        s2.invariants(),
{
}

/// Theorem: The OS-level map operation refines the high-level map operation.
proof fn os_map_refines_hl_map(s1: OSMemoryState, s2: OSMemoryState, op: MapOp)
    requires
        s1.invariants(),
        OSMemoryState::map(s1, s2, op),
    ensures
        HlMemoryState::map(s1@, s2@, op),
{
    lemma_interpret_pt_mem_equals_all_mappings(s2);
    lemma_interpret_pt_mem_equals_all_mappings(s1);
    // Post condition satified because interpret_pt_mem equals all_mappings (lemma).
    // Then updating pt_mem is equivalent to updating all_mappings.
}

/// Theorem. The OS-level unmap operation preserves the invariants.
proof fn os_unmap_preserves_invariants(s1: OSMemoryState, s2: OSMemoryState, op: UnmapOp)
    requires
        s1.invariants(),
        OSMemoryState::unmap(s1, s2, op),
    ensures
        s2.invariants(),
{
}

/// Theorem: The OS-level unmap operation refines the high-level unmap operation.
proof fn os_unmap_refines_hl_unmap(s1: OSMemoryState, s2: OSMemoryState, op: UnmapOp)
    requires
        s1.invariants(),
        OSMemoryState::unmap(s1, s2, op),
    ensures
        HlMemoryState::unmap(s1@, s2@, op),
{
    lemma_interpret_pt_mem_equals_all_mappings(s2);
    lemma_interpret_pt_mem_equals_all_mappings(s1);
    // Post condition satified because interpret_pt_mem equals all_mappings (lemma).
    // Then updating pt_mem is equivalent to updating all_mappings.    
}

} // verus!
