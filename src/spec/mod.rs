use vstd::prelude::*;

pub mod addr;
pub mod hl;
pub mod mem;
pub mod os;
pub mod s1pt;
pub mod s2pt;

verus! {

/// Convert `nat` to `u64`.
pub open spec fn nat_to_u64(v: nat) -> u64
    recommends
        v <= u64::MAX,
{
    v as u64
}

} // verus!
