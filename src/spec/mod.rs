use vstd::prelude::*;

pub mod addr;
pub mod arch;
pub mod frame;
pub mod hardware;
pub mod high_level;
pub mod low_level;
pub mod pt_mem;
pub mod pt_spec;

verus! {

/// Convert `nat` to `u64`.
pub open spec fn nat_to_u64(v: nat) -> u64
    recommends
        v <= u64::MAX,
{
    v as u64
}

} // verus!
