use vstd::prelude::*;

mod hardware;
mod hl;
mod mem;
mod os;
mod pt;
mod s1pt;
mod s2pt;

verus! {

/// If `addr` is aligned to `size`.
pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}

/// If region (base1, size1) and region (base2, size2) overlap.
pub open spec(checked) fn overlap(base1: nat, size1: nat, base2: nat, size2: nat) -> bool {
    if base1 <= base2 {
        base2 < base1 + size1
    } else {
        base1 < base2 + size2
    }
}

/// If `a` is in the range `[lb, ub)` i.e. `lb <= a < ub`.
pub open spec(checked) fn between(a: nat, lb: nat, ub: nat) -> bool {
    lb <= a < ub
}

/// Calc the word index of `addr`.
pub open spec(checked) fn word_index(addr: nat) -> nat {
    addr / 8
}

} // verus!
