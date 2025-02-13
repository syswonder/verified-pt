use vstd::prelude::*;

mod hardware;
mod os;
mod pt;
mod mem;
mod s1pt;
mod s2pt;

verus! {

/// If `addr` is aligned to `size`
pub open spec(checked) fn aligned(addr: nat, size: nat) -> bool {
    addr % size == 0
}

} // verus!