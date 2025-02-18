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

use super::{
    between,
    mem::{Frame, RwOp},
    word_index,
};

verus! {

/// High level memory state.
pub struct HlMemoryState {
    /// Word-indexed memory (vmem_word_idx -> word value).
    pub mem: Map<nat, nat>,
    
    /// Mappings from virtual address to physical frames (virtual page base addr -> physical frame).
    ///
    /// The key must be the base address of a virtual page i.e. [`key`, `key + frame.size`)
    /// must be mapped to the same frame.
    pub mappings: Map<nat, Frame>,
}

impl HlMemoryState {
    /// Virtual memory domain covered by `self.mappings`.
    pub open spec fn mem_domain_covered_by_mappings(self) -> Set<nat> {
        Set::new(
            |vmem_word_idx: nat|
                exists|base: nat, frame: Frame|
                    {
                        &&& #[trigger] self.mappings.contains_pair(base, frame)
                        &&& between(vmem_word_idx * 8, base, base)
                    },
        )
    }

    /// Init state. Empty memory and no mappings.
    pub open spec fn init(self) -> bool {
        &&& self.mem === Map::empty()
        &&& self.mappings === Map::empty()
    }

    /// State transition - Read & Write
    pub open spec fn read_write(
        s1: Self,
        s2: Self,
        vaddr: nat,
        op: RwOp,
        mapping: Option<(nat, Frame)>,
    ) -> bool {
        let vmem_word_idx = word_index(vaddr);
        
        // Mappings should be unchanged
        &&& s1.mappings === s2.mappings

        // Check memory operation
        &&& match mapping {
            Some((base, frame)) => {
                // If `mapping` is `Some`, `s1.mappings` should contain it
                &&& s1.mappings.contains_pair(
                    base,
                    frame,
                )
                // `vaddr` should be in the virtual page marked by `base`
                &&& between(
                    vaddr,
                    base,
                    base + frame.size.to_nat(),
                )
                // Memory operation
                &&& match op {
                    RwOp::Read { result } => {
                        // Memory should be unchanged
                        &&& s1.mem === s2.mem
                        // Check frame attributes
                        &&& if !frame.attr.readable || !frame.attr.user_accessible {
                            // If the frame is not readable or user accessible, the
                            // result should be `PageFault`
                            result is PageFault
                        } else {
                            // Otherwise, the result should be `Ok`
                            &&& result is Ok
                            // The value should be the value in the memory at `vmem_word_idx`
                            &&& result->0 === s1.mem[vmem_word_idx]
                        }
                    }
                    RwOp::Write { value, result } => {
                        // Check frame attributes
                        if !frame.attr.writable || !frame.attr.user_accessible {
                            // If the frame is not writable or user accessible, the
                            // result should be `PageFault`
                            &&& result is PageFault
                            // Memory should be unchanged
                            &&& s1.mem === s2.mem
                        } else {
                            // Otherwise, the result should be `Ok`
                            &&& result is Ok
                            // Memory should be updated at `vmem_word_idx` with `value`
                            &&& s1.mem === s2.mem.insert(vmem_word_idx, value)
                        }
                    }
                }
            },
            None => {
                // If `mapping` is `None`, the memory domain should not contain `vmem_word_idx`
                &&& !s1.mem_domain_covered_by_mappings().contains(
                    vmem_word_idx,
                )
                // And memory should be unchanged
                &&& s1.mem === s2.mem
                // Result should be `PageFault`
                &&& match op {
                    RwOp::Read { result } => result is PageFault,
                    RwOp::Write { result, .. } => result is PageFault,
                }
            },
        }
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
