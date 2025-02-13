//! Page-table-level state transition specification.
//!
//! The page table interface spec is written in such a way that it guarantees that the
//! impl behaves accordingto the state machine, and then in the memory state machine
//! we use these definitions.
//!
//! Page table state transition step includes:
//!
//! - Map
//! - Unmap
//! - Resolve
//! - ...
use vstd::prelude::*;

use super::mem::OSMemoryState;

verus! {

impl OSMemoryState {

}

} // verus!
