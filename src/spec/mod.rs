use vstd::prelude::*;

mod addr;
mod hardware;
mod hl;
mod mem;
mod os;
mod pt;
mod s1pt;
mod s2pt;

verus! {

/// Convert `nat` to `u64`.
pub open spec fn nat_to_u64(v: nat) -> u64
    recommends
        v <= u64::MAX,
{
    v as u64
}

} // verus!
