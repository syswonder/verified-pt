use vstd::prelude::*;

pub mod addr;
pub mod arch;
pub mod frame;
pub mod hardware;
pub mod high_level;
pub mod low_level;
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

/// View a slice as a `Seq`
pub open spec fn slice_to_seq<T>(v: &[T]) -> Seq<T> {
    Seq::new(v.len() as nat, |i| v[i])
}

} // verus!
