//! Basic lemmas used by the proof.
use vstd::prelude::*;

use crate::common::{
    addr::{PAddr, VAddr, WORD_SIZE},
    frame::{Frame, FrameSize},
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
    by (nonlinear_arith)
    requires
        vaddr.aligned(fsize.as_nat()),
    ensures
        vaddr.aligned(WORD_SIZE),
{
}

/// Lemma. PA alignment to FrameSize ensures alignment to WORD_SIZE.
pub proof fn lemma_pa_align_frame_size_must_align_word_size(paddr: PAddr, fsize: FrameSize)
    by (nonlinear_arith)
    requires
        paddr.aligned(fsize.as_nat()),
    ensures
        paddr.aligned(WORD_SIZE),
{
}

/// Lemma. PAddr inequality implies PIdx inequality.
pub proof fn lemma_paddr_neq_implies_pidx_neq(paddr1: PAddr, paddr2: PAddr)
    requires
        paddr1.0 < paddr2.0,
        paddr2.aligned(WORD_SIZE),
    ensures
        paddr1.idx().0 < paddr2.idx().0,
{
}

/// Lemma. VAddr within virtual page implies PAddr within physical frame.
pub proof fn lemma_vaddr_in_vpage_implies_paddr_in_pframe(vaddr: VAddr, vbase: VAddr, frame: Frame)
    requires
        vaddr.within(vbase, frame.size.as_nat()),
    ensures
        vaddr.map(vbase, frame.base).within(frame.base, frame.size.as_nat()),
{
}

/// Lemma. `a % WORD_SIZE == 0` and `b % WORD_SIZE == 0` implies `(a + b) % WORD_SIZE == 0`.
pub proof fn lemma_sum_align_word_size(a: nat, b: nat)
    by (nonlinear_arith)
    requires
        a % WORD_SIZE == 0,
        b % WORD_SIZE == 0,
    ensures
        (a + b) % WORD_SIZE == 0,
{
}

/// Lemma. If a seqence does not contain a value, then its subsequence does not contain it either.
pub proof fn lemma_not_in_seq_implies_not_in_subseq<T>(
    seq1: Seq<T>,
    seq2: Seq<T>,
    start: T,
    needle: T,
)
    requires
        seq1 == seq![start].add(seq2),
        !seq1.contains(needle),
    ensures
        start != needle,
        !seq2.contains(needle),
{
    assert(seq1[0] == start);
    assert(seq1.contains(seq1[0]));
    if seq2.contains(needle) {
        let i = choose|i| 0 <= i < seq2.len() && seq2[i] == needle;
        assert(seq1[i + 1] == needle);
        assert(seq1.contains(needle));
    }
}

} // verus!
