//! Prove that OS state machine refines the high-level state machine.
use crate::spec::{
    addr::VAddr,
    mem::{Frame, ReadOp},
    os::OSMemoryState,
};
use vstd::prelude::*;

verus! {

/// Lemma: The equality of 2 sets.
proof fn lemma_set_eq<A>(s1: Set<A>, s2: Set<A>)
    requires
        forall|a| s1.contains(a) ==> s2.contains(a),
        forall|a| s2.contains(a) ==> s1.contains(a),
    ensures
        s1 === s2,
{
    assert(s1 === s2)
}

/// Lemma: The equality of 2 maps.
proof fn lemma_map_eq_base<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    requires
        forall|k| m1.contains_key(k) ==> m2.contains_key(k),
        forall|k| m2.contains_key(k) ==> m1.contains_key(k),
        forall|k| #[trigger] m1.contains_key(k) ==> m1[k] === m2[k],
    ensures
        m1 === m2,
{
    assert(m1 === m2)
}

/// Lemma: The equality of 2 maps.
proof fn lemma_map_eq<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    requires
        forall|k, v| m1.contains_pair(k, v) ==> m2.contains_pair(k, v),
        forall|k, v| m2.contains_pair(k, v) ==> m1.contains_pair(k, v),
    ensures
        m1 === m2,
{
    assert forall|k| m1.contains_key(k) implies m2.contains_key(k) by {
        assert(m2.contains_pair(k, m1[k]));
    };
    assert forall|k| m2.contains_key(k) implies m1.contains_key(k) by {
        assert(m1.contains_pair(k, m2[k]));
    };
    assert forall|k| #[trigger] m1.contains_key(k) implies m1[k] === m2[k] by {
        let v = m1.index(k);
        assert(m1.contains_pair(k, v));
        assert(m2.contains_pair(k, v));
    }
    assert(m1 === m2) by {
        lemma_map_eq_base(m1, m2);
    }
}

/// Lemma: If the TLB is a subset of the page table, then the interpreted page table
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

    // 1. Prove that any mapping in `all_mappings` is also in `pt_mem`.
    assert(forall|addr, frame| #[trigger]
        all_mappings.contains_pair(addr, frame) ==> pt_mem.contains_pair(addr, frame));

    // 2. Prove that any mapping in `pt_mem` is also in `all_mappings`.
    assert forall|addr, frame| #[trigger]
        pt_mem.contains_pair(addr, frame) implies all_mappings.contains_pair(addr, frame) by {
        if tlb.contains_key(addr) {
            assert(all_mappings.contains_pair(addr, tlb[addr]));
        } else {
            assert(all_mappings.contains_pair(addr, pt_mem[addr]));
        }
    }

    // 3. Prove that the two maps are equal.
    lemma_map_eq(pt_mem, all_mappings);
}

proof fn os_init_refines_hl_init(st: OSMemoryState)
    requires
        st.tlb_is_submap_of_pt(),
        st.init(),
    ensures
        st@.init(),
{
    lemma_interpret_pt_mem_equals_all_mappings(st);
    assert(st@.mappings =~= Map::empty());
}

proof fn os_read_refines_hl_read(
    s1: OSMemoryState,
    s2: OSMemoryState,
    op: ReadOp,
    mapping: Option<(VAddr, Frame)>,
) {
}

} // verus!
