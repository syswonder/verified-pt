//! Specification of the page table module, consisting of
//!
//! - High-level. Abstracts the whole memory management module, acts as the proof target.
//! - Hardware. Specifies the harware MMU behavior.
//! - Page table. Defines the implementation target of the page table.
//! - Low-level. Acts as a bridge between the implementation and the high-level specification.
use vstd::prelude::*;

pub mod hardware;
pub mod high_level;
pub mod low_level;
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
