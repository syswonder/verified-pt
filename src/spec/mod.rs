use vstd::prelude::*;

mod hardware;
mod hl;
mod mem;
mod os;
mod pt;
mod s1pt;
mod s2pt;

verus! {

/// If `addr` is aligned to `size`
pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}

} // verus!
