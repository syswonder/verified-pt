use vstd::prelude::*;

pub mod addr;
pub mod arch;
pub mod frame;
pub mod hardware;
pub mod high_level;
pub mod low_level;
pub mod op;
pub mod pt_spec;
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

/// If `v` is power of 2.
pub open spec fn is_pow2(v: nat) -> bool
    recommends
        v <= u64::MAX,
{
    let u64v = v as u64;
    (u64v & (u64v - 1) as u64) == 0
}

} // verus!
