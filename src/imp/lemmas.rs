//! Basic lemmas used by the proof.
use vstd::prelude::*;

use crate::common::{
    addr::{PAddr, VAddr},
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

/// Lemma. VA alignment to FrameSize ensures alignment to 8.
pub proof fn lemma_va_align_frame_size_must_align_8(vaddr: VAddr, fsize: FrameSize)
    by (nonlinear_arith)
    requires
        vaddr.aligned(fsize.as_nat()),
    ensures
        vaddr.aligned(8),
{
}

/// Lemma. PA alignment to FrameSize ensures alignment to 8.
pub proof fn lemma_pa_align_frame_size_must_align_8(paddr: PAddr, fsize: FrameSize)
    by (nonlinear_arith)
    requires
        paddr.aligned(fsize.as_nat()),
    ensures
        paddr.aligned(8),
{
}

/// Lemma. PAddr inequality implies PIdx inequality.
pub proof fn lemma_paddr_neq_implies_pidx_neq(paddr1: PAddr, paddr2: PAddr)
    requires
        paddr1.0 < paddr2.0,
        paddr2.aligned(8),
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

/// Lemma. `a % 8 == 0` and `b % 8 == 0` implies `(a + b) % 8 == 0`.
pub proof fn lemma_sum_align_8(a: nat, b: nat)
    by (nonlinear_arith)
    requires
        a % 8 == 0,
        b % 8 == 0,
    ensures
        (a + b) % 8 == 0,
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

/// Lemma. If a sequence is a zero sequence, then its sum is zero.
pub proof fn lemma_zero_seq_sum_is_zero(s: Seq<nat>)
    requires
        s == seq![0nat; s.len()],
    ensures
        s.fold_right(|part: nat, sum: nat| part + sum, 0nat) == 0,
    decreases s.len(),
{
    let f = |part: nat, sum: nat| part + sum;
    let sum = s.fold_right(f, 0nat);
    if s.len() == 0 {
        assert(sum == 0);
    } else {
        let sub = s.subrange(0, s.len() - 1);
        assert(sub == seq![0nat; sub.len()]);
        assert(sum == sub.fold_right(f, s.last()));
        lemma_zero_seq_sum_is_zero(sub);
    }
}

/// Lemma. Left sum is equal to right sum (fold_right_alt).
proof fn lemma_left_sum_eq_right_sum_alt(s: Seq<nat>)
    ensures
        s.fold_left(0nat, |sum: nat, part: nat| sum + part) == s.fold_right_alt(
            |part: nat, sum: nat| part + sum,
            0nat,
        ),
    decreases s.len(),
{
    let lsum = s.fold_left(0nat, |sum: nat, part: nat| sum + part);
    let rsum = s.fold_right_alt(|part: nat, sum: nat| part + sum, 0nat);
    if s.len() > 0 {
        let lsub = s.subrange(0, s.len() - 1);
        let lsub_lsum = lsub.fold_left(0nat, |sum: nat, part: nat| sum + part);
        let lsub_rsum = lsub.fold_right_alt(|part: nat, sum: nat| part + sum, 0nat);
        assert(lsum == lsub_lsum + s.last());

        let rsub = s.subrange(1, s.len() as int);
        let rsub_lsum = rsub.fold_left(0nat, |sum: nat, part: nat| sum + part);
        let rsub_rsum = rsub.fold_right_alt(|part: nat, sum: nat| part + sum, 0nat);

        assert(rsum == s[0] + rsub.fold_right_alt(|part: nat, sum: nat| part + sum, 0nat));

        lemma_left_sum_eq_right_sum_alt(lsub);
        lemma_left_sum_eq_right_sum_alt(rsub);
        assert(lsub_lsum == lsub_rsum);

        if lsub.len() > 0 {
            let lsub_rsub = lsub.subrange(1, lsub.len() as int);
            assert(lsub_rsum == lsub.first() + lsub_rsub.fold_right_alt(
                |part: nat, sum: nat| part + sum,
                0nat,
            ));
            let rsub_lsub = rsub.subrange(0, rsub.len() - 1);
            assert(rsub_lsum == rsub.last() + rsub_lsub.fold_left(
                0nat,
                |sum: nat, part: nat| sum + part,
            ));
            assert(lsub_rsub == rsub_lsub);

            lemma_left_sum_eq_right_sum_alt(lsub_rsub);
            let sub_sub_sum = lsub_rsub.fold_right_alt(|part: nat, sum: nat| part + sum, 0nat);

            assert(lsum == s.last() + s.first() + sub_sub_sum);
            assert(rsum == s.first() + s.last() + sub_sub_sum);

            assert(lsum == rsum);
        }
    }
}

/// Lemma. Left sum is equal to right sum.
pub proof fn lemma_left_sum_eq_right_sum(s: Seq<nat>)
    ensures
        s.fold_left(0nat, |sum: nat, part: nat| sum + part) == s.fold_right(
            |part: nat, sum: nat| part + sum,
            0nat,
        ),
{
    lemma_left_sum_eq_right_sum_alt(s);
    s.lemma_fold_right_alt(|part: nat, sum: nat| part + sum, 0nat);
}

/// Lemma. If all parts align to a value, then the sum of the parts aligns to the same value.
pub proof fn lemma_parts_align_implies_sum_align(s: Seq<nat>, align: nat)
    by (nonlinear_arith)
    requires
        align > 0,
        forall|i| 0 <= i < s.len() ==> s[i] % align == 0,
    ensures
        s.fold_left(0nat, |sum: nat, part: nat| sum + part) % align == 0,
    decreases s.len(),
{
    let sum = s.fold_left(0nat, |sum: nat, part: nat| sum + part);
    if s.len() > 0 {
        let sub = s.subrange(0, s.len() - 1);
        let sub_sum = sub.fold_left(0nat, |sum: nat, part: nat| sum + part);
        lemma_parts_align_implies_sum_align(sub, align);
        assert(sum == sub_sum + s.last());
        vstd::arithmetic::div_mod::lemma_add_mod_noop(
            sub_sum as int,
            s.last() as int,
            align as int,
        );
    }
}

/// Lemma. If two ranges are aligned, then their start and end are equal.
pub proof fn lemma_aligned_range_eq(a: nat, b: nat, m: nat, align: nat)
    by (nonlinear_arith)
    requires
        a <= m < a + align,
        b <= m < b + align,
        align > 0,
        a % align == b % align,
    ensures
        a == b,
{
    let x = a / align;
    let y = b / align;
    let z = a % align;
    assert(z < align);
    assert(a == x * align + z);
    assert(b == y * align + z);
    assert(x * align + z <= m < (x + 1) * align + z);
    assert(y * align + z <= m < (y + 1) * align + z);
    assert(x == y);
}

} // verus!
