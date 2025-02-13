//! OS-level memory state transtition specification.
//! 
//! OS level is the highest level of memory state transition specification, which describes
//! how the whole memory system behaves.
//! 
//! OS state transition step includes
//! 
//! - Hardware-level operations
//! - page table map & unmap
//! - ...

use vstd::prelude::*;

use super::mem::OSMemoryState;

verus! {

impl OSMemoryState {
    
}

} // verus!