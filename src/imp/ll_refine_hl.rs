//! Prove the low-level state machine refines the high-level state machine.
use vstd::prelude::*;

use super::lemmas::*;
use crate::spec::{
    addr::{PAddr, VAddr, VIdx, WORD_SIZE},
    frame::Frame,
    high_level::HighLevelState,
    low_level::LowLevelState,
    op::{MapOp, QueryOp, ReadOp, TLBEvictOp, TLBFillOp, UnmapOp, WriteOp},
};

verus! {

/// Lemma. If the TLB is a subset of the page table, then the interpreted page table
/// is equal to the all mappings (page table & TLB).
proof fn lemma_interpret_pt_equals_all_mappings(st: LowLevelState)
    requires
        st.tlb_is_submap_of_pt(),
    ensures
        st.pt.interpret() === st.all_mappings(),
{
    let interp_pt = st.pt.interpret();
    let tlb = st.tlb;
    let all_mappings = st.all_mappings();

    // 1. Any mapping in `all_mappings` is also in `interp_pt`.
    assert(forall|addr, frame| #[trigger]
        all_mappings.contains_pair(addr, frame) ==> interp_pt.contains_pair(addr, frame));

    // 2. Any mapping in `interp_pt` is also in `all_mappings`.
    assert forall|addr, frame| #[trigger]
        interp_pt.contains_pair(addr, frame) implies all_mappings.contains_pair(addr, frame) by {
        if tlb.contains_key(addr) {
            assert(all_mappings.contains_pair(addr, tlb[addr]));
        } else {
            assert(all_mappings.contains_pair(addr, interp_pt[addr]));
        }
    }

    // 3. The two maps are equal.
    lemma_map_eq_pair(interp_pt, all_mappings);
}

/// Lemma. If there is no overlap in the virtual memory space, then there is at most
/// one mapping containing a virtual address.
proof fn lemma_at_most_one_mapping_for_vaddr(st: LowLevelState, vaddr: VAddr)
    requires
        st.mappings_nonoverlap_in_vmem(),
    ensures
        forall|base1, frame1, base2, frame2|
            {
                &&& #[trigger] st.pt.interpret().contains_pair(base1, frame1)
                &&& vaddr.within(base1, frame1.size.as_nat())
                &&& #[trigger] st.pt.interpret().contains_pair(base2, frame2)
                &&& vaddr.within(base2, frame2.size.as_nat())
            } ==> base1 == base2,
{
    if exists|base1, frame1, base2, frame2|
        {
            &&& #[trigger] st.pt.interpret().contains_pair(base1, frame1)
            &&& vaddr.within(base1, frame1.size.as_nat())
            &&& #[trigger] st.pt.interpret().contains_pair(base2, frame2)
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
                &&& #[trigger] st.pt.interpret().contains_pair(base1, frame1)
                &&& vaddr.within(base1, frame1.size.as_nat())
                &&& #[trigger] st.pt.interpret().contains_pair(base2, frame2)
                &&& vaddr.within(base2, frame2.size.as_nat())
                &&& base1 != base2
            };
        assert(VAddr::overlap(base1, frame1.size.as_nat(), base2, frame2.size.as_nat()));
    }
}

/// Lemma. If there is no overlap in the physical memory space, then 2 different virtual
/// indexes cannot map to the same physical index.
proof fn lemma_different_pidxs_for_different_vidxs(st: LowLevelState, vidx1: VIdx, vidx2: VIdx)
    requires
        st.mappings_nonoverlap_in_pmem(),
        st.mappings_aligned(),
        vidx1 != vidx2,
    ensures
        forall|base1: VAddr, frame1: Frame, base2: VAddr, frame2: Frame|
            {
                &&& #[trigger] st.pt.interpret().contains_pair(base1, frame1)
                &&& vidx1.addr().within(base1, frame1.size.as_nat())
                &&& #[trigger] st.pt.interpret().contains_pair(base2, frame2)
                &&& vidx2.addr().within(base2, frame2.size.as_nat())
            } ==> vidx1.addr().map(base1, frame1.base).idx() != vidx2.addr().map(
                base2,
                frame2.base,
            ).idx(),
{
    if exists|base1, frame1, base2, frame2|
        {
            &&& #[trigger] st.pt.interpret().contains_pair(base1, frame1)
            &&& vidx1.addr().within(base1, frame1.size.as_nat())
            &&& #[trigger] st.pt.interpret().contains_pair(base2, frame2)
            &&& vidx2.addr().within(base2, frame2.size.as_nat())
            &&& vidx1.addr().map(base1, frame1.base).idx() == vidx2.addr().map(
                base2,
                frame2.base,
            ).idx()
        } {
        // Proof by contradiction.
        let (base1, frame1, base2, frame2): (VAddr, Frame, VAddr, Frame) = choose|
            base1,
            frame1,
            base2,
            frame2,
        |
            {
                &&& #[trigger] st.pt.interpret().contains_pair(base1, frame1)
                &&& vidx1.addr().within(base1, frame1.size.as_nat())
                &&& #[trigger] st.pt.interpret().contains_pair(base2, frame2)
                &&& vidx2.addr().within(base2, frame2.size.as_nat())
                &&& vidx1.addr().map(base1, frame1.base).idx() == vidx2.addr().map(
                    base2,
                    frame2.base,
                ).idx()
            };
        assert(PAddr::overlap(
            frame1.base,
            frame1.size.as_nat(),
            frame2.base,
            frame2.size.as_nat(),
        ));
    }
}

/// Lemma. If there is no overlap in the physical memory space, adding a new mapping that
/// does not overlap with existing mappings preserves the non-overlap property.
proof fn lemma_add_mapping_preserves_nonoverlap(
    mappings: Map<VAddr, Frame>,
    base: VAddr,
    frame: Frame,
)
    requires
        forall|base1: VAddr, frame1: Frame, base2: VAddr, frame2: Frame|
            mappings.contains_pair(base1, frame1) && mappings.contains_pair(base2, frame2) ==> ((
            base1 == base2) || !PAddr::overlap(
                frame1.base,
                frame1.size.as_nat(),
                frame2.base,
                frame2.size.as_nat(),
            )),
        !exists|frame1: Frame|
            {
                &&& #[trigger] mappings.contains_value(frame1)
                &&& PAddr::overlap(
                    frame1.base,
                    frame1.size.as_nat(),
                    frame.base,
                    frame.size.as_nat(),
                )
            },
    ensures
        forall|base1: VAddr, frame1: Frame, base2: VAddr, frame2: Frame|
            mappings.insert(base, frame).contains_pair(base1, frame1) && mappings.insert(
                base,
                frame,
            ).contains_pair(base2, frame2) ==> ((base1 == base2) || !PAddr::overlap(
                frame1.base,
                frame1.size.as_nat(),
                frame2.base,
                frame2.size.as_nat(),
            )),
{
    assert forall|base1: VAddr, frame1: Frame, base2: VAddr, frame2: Frame|
        mappings.insert(base, frame).contains_pair(base1, frame1) && mappings.insert(
            base,
            frame,
        ).contains_pair(base2, frame2) implies ((base1 == base2) || !PAddr::overlap(
        frame1.base,
        frame1.size.as_nat(),
        frame2.base,
        frame2.size.as_nat(),
    )) by {
        if base1 != base2 {
            if base1 == base {
                // New mapping doesn't overlap with frame2
                assert(mappings.contains_value(frame2));
                assert(!PAddr::overlap(
                    frame.base,
                    frame.size.as_nat(),
                    frame2.base,
                    frame2.size.as_nat(),
                ));
            } else if base2 == base {
                // New mapping doesn't overlap with frame1
                assert(mappings.contains_value(frame1));
                assert(!PAddr::overlap(
                    frame.base,
                    frame.size.as_nat(),
                    frame1.base,
                    frame1.size.as_nat(),
                ));
            } else {
                // Old mappings don't overlap
                assert(mappings.contains_pair(base1, frame1));
                assert(mappings.contains_pair(base2, frame2));
            }
        }
    }
}

/// Theorem. The low-level init state implies the invariants.
proof fn ll_init_implies_invariants(st: LowLevelState)
    requires
        st.init(),
    ensures
        st.invariants(),
{
}

/// Theorem. The low-level init state refines the high-level init state.
proof fn ll_init_refines_hl_init(st: LowLevelState)
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

/// Theorem. The low-level read operation preserves the invariants.
proof fn ll_read_preserves_invariants(s1: LowLevelState, s2: LowLevelState, op: ReadOp)
    requires
        s1.invariants(),
        LowLevelState::read(s1, s2, op),
    ensures
        s2.invariants(),
{
}

/// Theorem. The low-level read operation refines the high-level read operation.
proof fn ll_read_refines_hl_read(s1: LowLevelState, s2: LowLevelState, op: ReadOp)
    requires
        s1.invariants(),
        LowLevelState::read(s1, s2, op),
    ensures
        HighLevelState::read(s1@, s2@, op),
{
    // Lemmas satisfied by the invariants.
    lemma_interpret_pt_equals_all_mappings(s1);
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

/// Theorem. The low-level write operation preserves the invariants.
proof fn ll_write_preserves_invariants(s1: LowLevelState, s2: LowLevelState, op: WriteOp)
    requires
        s1.invariants(),
        LowLevelState::write(s1, s2, op),
    ensures
        s2.invariants(),
{
    assert(s1.pt.interpret() === s2.pt.interpret());
}

/// Theorem. The low-level write operation refines the high-level write operation.
proof fn ll_write_refines_hl_write(s1: LowLevelState, s2: LowLevelState, op: WriteOp)
    requires
        s1.invariants(),
        LowLevelState::write(s1, s2, op),
    ensures
        HighLevelState::write(s1@, s2@, op),
{
    // Lemmas satisfied by the invariants.
    lemma_interpret_pt_equals_all_mappings(s1);
    lemma_at_most_one_mapping_for_vaddr(s2, op.vaddr);

    match op.mapping {
        Some((base, frame)) => {
            let vidx = op.vaddr.idx();
            let pidx = op.vaddr.map(base, frame.base).idx();

            if pidx.0 < s1.mem.len() && frame.attr.writable && frame.attr.user_accessible {
                // `s1` has the mapping `(base, frame)` which contains `op.vaddr`.
                assert(s1.all_mappings().contains_pair(base, frame));
                assert(op.vaddr.within(base, frame.size.as_nat()));

                // Prove that the interpreted memory is updated correctly.
                assert forall|vidx2: VIdx|
                    s2.interpret_mem().contains_key(vidx2) && s1.interpret_mem().insert(
                        vidx,
                        op.value,
                    ).contains_key(vidx2) implies #[trigger] s2.interpret_mem()[vidx2]
                    == s1.interpret_mem().insert(vidx, op.value)[vidx2] by {
                    if vidx2 == vidx {
                        // Prove that value at `vidx` is updated.
                        //
                        // Value updated in the physical memory is the same as in the interpreted memory,
                        // because there is only one mapping for `op.vaddr` (lemma).
                        assert(s2.interpret_mem()[vidx] == op.value);
                    } else {
                        // Prove that values at other indices are unchanged.
                        let (base2, frame2) = choose|base2: VAddr, frame2: Frame|
                            {
                                &&& #[trigger] s1.all_mappings().contains_pair(base2, frame2)
                                &&& vidx2.addr().within(base2, frame2.size.as_nat())
                                &&& vidx2.addr().map(base2, frame2.base).idx().0 < s1.mem.len()
                            };
                        let pidx2 = vidx2.addr().map(base2, frame2.base).idx();
                        // Only `interpret_mem()[vidx]` and `mem[pidx]` are updated.
                        //
                        // Lemma ensures that `pidx` and `pidx2` are different for different `vidx` and `vidx2`.
                        // Thus `mem[pidx2]` is not updated.
                        lemma_different_pidxs_for_different_vidxs(s1, vidx, vidx2);
                        assert(s1.mem[pidx2.as_int()] == s2.mem[pidx2.as_int()]);
                    }
                }
                assert(s2.interpret_mem() === s1.interpret_mem().insert(op.vaddr.idx(), op.value));
            }
        },
        None => {
            // Satisfied because interpret_pt_mem equals all_mappings (lemma).
            assert(!s1@.mem_domain_covered_by_mappings().contains(op.vaddr.idx()));
        },
    }
}

/// Theorem. The low-level map operation preserves the invariants.
proof fn ll_map_preserves_invariants(s1: LowLevelState, s2: LowLevelState, op: MapOp)
    requires
        s1.invariants(),
        LowLevelState::map(s1, s2, op),
    ensures
        s2.invariants(),
{
    if s2.pt.interpret() == s1.pt.interpret().insert(op.vaddr, op.frame) {
        // Prove mappings aligned to word size.
        assert forall|base: VAddr, frame: Frame| #[trigger]
        s2.pt.interpret().contains_pair(base, frame) implies base.aligned(WORD_SIZE)
        && frame.base.aligned(WORD_SIZE) by {
            if base == op.vaddr {
                lemma_va_align_frame_size_must_align_word_size(op.vaddr);
                lemma_pa_align_frame_size_must_align_word_size(op.frame.base);
                assert(base.aligned(WORD_SIZE));
                assert(frame.base.aligned(WORD_SIZE));
            } else {
                assert(s1.pt.interpret().contains_pair(base, frame));
            }
        }
        // Prove mappings within physical memory.
        assert forall|base: VAddr, frame: Frame| #[trigger]
        s2.pt.interpret().contains_pair(base, frame) implies frame.base.0 + frame.size.as_nat()
        <= s2.mem.len() by {
            if base == op.vaddr {
                assert(op.frame.base.0 + op.frame.size.as_nat() <= s2.mem.len());
            } else {
                assert(s1.pt.interpret().contains_pair(base, frame));
            }
        }
    }
    assert(s2.mappings_aligned());
    assert(s2.frames_within_pmem());
    
    // Prove non-overlapping mappings in pmem and vmem.
    assert(s2.mappings_nonoverlap_in_vmem());
    lemma_add_mapping_preserves_nonoverlap(s1.pt.interpret(), op.vaddr, op.frame);
    assert(s2.mappings_nonoverlap_in_pmem());

    // Prove tlb is a subset of pt.
    assert(s1.tlb == s1.hw_state().tlb);
    assert(forall|base, frame|
        s1.pt.interpret().contains_pair(base, frame) ==> s2.pt.interpret().contains_pair(
            base,
            frame,
        ));
    assert(s2.tlb_is_submap_of_pt());
}

/// Theorem. The low-level map operation refines the high-level map operation.
proof fn ll_map_refines_hl_map(s1: LowLevelState, s2: LowLevelState, op: MapOp)
    requires
        s1.invariants(),
        LowLevelState::map(s1, s2, op),
    ensures
        HighLevelState::map(s1@, s2@, op),
{
    lemma_interpret_pt_equals_all_mappings(s1);
    ll_map_preserves_invariants(s1, s2, op);
    lemma_interpret_pt_equals_all_mappings(s2);
    
    // Post condition satisfied because interpret_pt_mem equals all_mappings (lemma).
    // Then updating pt_mem is equivalent to updating all_mappings.
}

/// Theorem. The low-level unmap operation preserves the invariants.
proof fn ll_unmap_preserves_invariants(s1: LowLevelState, s2: LowLevelState, op: UnmapOp)
    requires
        s1.invariants(),
        LowLevelState::unmap(s1, s2, op),
    ensures
        s2.invariants(),
{
    // Prove s2.pt is a subset of s1.pt.
    assert(forall |base, frame| #[trigger]
        s2.pt.interpret().contains_pair(base, frame) ==> s1.pt.interpret
            ().contains_pair(base, frame));

    // Prove tlb is a subset of pt.
    assert(s1.tlb == s1.hw_state().tlb);
    // s1.tlb < s1.pt ==> s2.tlb < s1.tlb\{op.vaddr} < s1.pt\{op.vaddr} = s2.pt
    assert forall|base, frame|
        #[trigger] s2.tlb.contains_pair(base, frame) implies s2.pt.interpret().contains_pair(
            base,
            frame,
        ) by {
            assert(s1.pt.interpret().contains_pair(base, frame));
        }
    assert(s2.tlb_is_submap_of_pt());
}

/// Theorem. The low-level unmap operation refines the high-level unmap operation.
proof fn ll_unmap_refines_hl_unmap(s1: LowLevelState, s2: LowLevelState, op: UnmapOp)
    requires
        s1.invariants(),
        LowLevelState::unmap(s1, s2, op),
    ensures
        HighLevelState::unmap(s1@, s2@, op),
{
    lemma_interpret_pt_equals_all_mappings(s1);
    ll_unmap_preserves_invariants(s1, s2, op);
    lemma_interpret_pt_equals_all_mappings(s2);

    // Post condition satisfied because interpret_pt_mem equals all_mappings (lemma).
    // Then updating pt_mem (low-level) is equivalent to updating all_mappings (high-level).
}

/// Theorem. The low-level query operation preserves the invariants.
proof fn ll_query_preserves_invariants(s1: LowLevelState, s2: LowLevelState, op: QueryOp)
    requires
        s1.invariants(),
        LowLevelState::query(s1, s2, op),
    ensures
        s2.invariants(),
{
    assert(s1.tlb == s1.hw_state().tlb);
}

/// Theorem. The low-level query operation refines the high-level query operation.
proof fn ll_query_refines_hl_query(s1: LowLevelState, s2: LowLevelState, op: QueryOp)
    requires
        s1.invariants(),
        LowLevelState::query(s1, s2, op),
    ensures
        HighLevelState::query(s1@, s2@, op),
{
    lemma_interpret_pt_equals_all_mappings(s1);
    ll_query_preserves_invariants(s1, s2, op);
    lemma_interpret_pt_equals_all_mappings(s2);

    // Post condition satisfied because interpret_pt_mem equals all_mappings (lemma).
    // Then querying pt_mem (low-level) is equivalent to querying all_mappings (high-level).
}

/// Theorem. The low-level tlb fill operation preserves the invariants.
proof fn ll_tlb_fill_preserves_invariants(s1: LowLevelState, s2: LowLevelState, op: TLBFillOp)
    requires
        s1.invariants(),
        LowLevelState::tlb_fill(s1, s2, op),
    ensures
        s2.invariants(),
{
}

/// Theorem. The low-level tlb fill operation refines the high-level identity operation.
proof fn ll_tlb_fill_refines_hl_id(s1: LowLevelState, s2: LowLevelState, op: TLBFillOp)
    requires
        s1.invariants(),
        LowLevelState::tlb_fill(s1, s2, op),
    ensures
        HighLevelState::id(s1@, s2@),
{
    lemma_interpret_pt_equals_all_mappings(s1);
    ll_tlb_fill_preserves_invariants(s1, s2, op);
    lemma_interpret_pt_equals_all_mappings(s2);

    // Post condition satisfied because TLB is the subset of the page table (lemma).
    // Then updating TLB has no effect on the page table.
}

/// Theorem. The low-level tlb evict operation preserves the invariants.
proof fn ll_tlb_evict_preserves_invariants(s1: LowLevelState, s2: LowLevelState, op: TLBEvictOp)
    requires
        s1.invariants(),
        LowLevelState::tlb_evict(s1, s2, op),
    ensures
        s2.invariants(),
{
}

/// Theorem. The low-level tlb evict operation refines the high-level identity operation.
proof fn ll_tlb_evict_refines_hl_id(s1: LowLevelState, s2: LowLevelState, op: TLBEvictOp)
    requires
        s1.invariants(),
        LowLevelState::tlb_evict(s1, s2, op),
    ensures
        HighLevelState::id(s1@, s2@),
{
    lemma_interpret_pt_equals_all_mappings(s1);
    ll_tlb_evict_preserves_invariants(s1, s2, op);
    lemma_interpret_pt_equals_all_mappings(s2);

    // Post condition satisfied because TLB is the subset of the page table (lemma).
    // Then updating TLB has no effect on the page table.
}

} // verus!
