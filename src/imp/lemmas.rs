//! Basic lemmas used by the proof.
use vstd::prelude::*;

use crate::spec::{
    addr::{PAddr, VAddr, WORD_SIZE},
    frame::FrameSize,
};

verus! {

/// Lemma. The equality of 2 sets. Two sets are equal if they have the same elements.
pub proof fn lemma_set_eq<A>(s1: Set<A>, s2: Set<A>)
    requires
        forall|a| s1.contains(a) ==> s2.contains(a),
        forall|a| s2.contains(a) ==> s1.contains(a),
    ensures
        s1 === s2,
{
    assert(s1 === s2)
}

/// Lemma. The equality of two maps. Two maps are equal if
/// - they have the same keys
/// - they have the same values for the same keys
pub proof fn lemma_map_eq_key_value<K, V>(m1: Map<K, V>, m2: Map<K, V>)
    requires
        forall|k| m1.contains_key(k) ==> m2.contains_key(k),
        forall|k| m2.contains_key(k) ==> m1.contains_key(k),
        forall|k| #[trigger] m1.contains_key(k) ==> m1[k] === m2[k],
    ensures
        m1 === m2,
{
    assert(m1 === m2)
}

/// Lemma. The equality of two maps. Two maps are equal if they have the same (key, value) pairs.
pub proof fn lemma_map_eq_pair<K, V>(m1: Map<K, V>, m2: Map<K, V>)
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
        lemma_map_eq_key_value(m1, m2);
    }
}

/// Lemma. VA alignment to FrameSize ensures alignment to WORD_SIZE.
pub proof fn lemma_va_align_frame_size_must_align_word_size(vaddr: VAddr, fsize: FrameSize)
    requires
        vaddr.aligned(fsize.as_nat()),
    ensures
        vaddr.aligned(WORD_SIZE),
{
    match fsize {
        FrameSize::Size4K => {
            assert(vaddr.aligned(4096));
            assert(vaddr.aligned(8));
        },
        FrameSize::Size2M => {
            assert(vaddr.aligned(2097152));
            assert(vaddr.aligned(8));
        },
        FrameSize::Size1G => {
            assert(vaddr.aligned(1073741824));
            assert(vaddr.aligned(8));
        },
    }
}

/// Lemma. PA alignment to FrameSize ensures alignment to WORD_SIZE.
pub proof fn lemma_pa_align_frame_size_must_align_word_size(paddr: PAddr, fsize: FrameSize)
    requires
        paddr.aligned(fsize.as_nat()),
    ensures
        paddr.aligned(WORD_SIZE),
{
    match fsize {
        FrameSize::Size4K => {
            assert(paddr.aligned(4096));
            assert(paddr.aligned(8));
        },
        FrameSize::Size2M => {
            assert(paddr.aligned(2097152));
            assert(paddr.aligned(8));
        },
        FrameSize::Size1G => {
            assert(paddr.aligned(1073741824));
            assert(paddr.aligned(8));
        },
    }
}

} // verus!
