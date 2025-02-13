//! High-level memory state machine & high level specifications.
//! 
//! To prove an implementation’s correctness we need to ask what we mean
//! by correctness. The application specification is a state machine encoding our
//! answer to that question. 
//! 
//! This specification represents the proof target. Our implementation running
//! in the intended environment should refine it. This is demonstrated in part
//! by the proof that the OS-level state machine refines this specification.

use vstd::prelude::*;

use super::mem::Frame;

verus! {

/// High level memory state.
pub struct HlMemoryState {
    /// Word-indexed memory.
    pub mem: Seq<nat>,
    /// Mappings from virtual addr to physical frames.
    pub mappings: Map<nat, Frame>,
}

impl HlMemoryState {
    /// State transition - Read & Write
    pub open spec fn read_write(s1: Self, s2: Self, vaddr: nat, write: bool) -> bool {
        // TODO
        true
    }

    /// State transtion - Map a virtual address to a frame.
    pub open spec fn map(s1: Self, s2: Self, vaddr: nat, frame: Frame) -> bool {
        // TODO
        true
    }

    /// State transtion - Unmap a virtual address.
    pub open spec fn unmap(s1: Self, s2: Self, vaddr: nat) -> bool {
        // TODO
        true
    }
}

} // verus!