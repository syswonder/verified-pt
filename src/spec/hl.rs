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
    mem::{Frame, FrameSize, MapOp, ReadOp, UnmapOp, WriteOp},
    PAddr, VAddr, VWordIdx,
};

verus! {

/// High level (abstract) memory state.
pub struct HlMemoryState {
    /// Word-indexed virtual memory (vword_idx -> word value).
    /// 
    /// We use word-index rather than address. Addresses that are not aligned to word boundaries should
    /// not be used to access a value, while word-indexes don't face the word-alignment issue.
    pub mem: Map<VWordIdx, nat>,
    /// Mappings from virtual address to physical frames (virtual page base addr -> physical frame).
    ///
    /// The key must be the base address of a virtual page i.e. virtual range [`key`, `key + frame.size`)
    /// must be mapped to the same physical frame.
    pub mappings: Map<VAddr, Frame>,
}

impl HlMemoryState {
    /// Virtual memory domain covered by `self.mappings`.
    pub open spec fn mem_domain_covered_by_mappings(self) -> Set<VWordIdx> {
        Set::new(
            |vword_idx: VWordIdx|
                exists|base: VAddr, frame: Frame|
                    {
                        &&& #[trigger] self.mappings.contains_pair(base, frame)
                        &&& vword_idx.addr().between(base, base.offset(frame.size.as_nat()))
                    },
        )
    }

    /// If `frame` overlaps with existing physical memory.
    pub open spec fn overlaps_pmem(self, frame: Frame) -> bool {
        exists|base: VAddr|
            {
                &&& #[trigger] self.mappings.contains_key(base)
                &&& PAddr::overlap(
                    self.mappings.index(base).base,
                    self.mappings.index(base).size.as_nat(),
                    frame.base,
                    frame.size.as_nat(),
                )
            }
    }

    /// If mapping `(vaddr, frame)` overlaps with existing virtual memory.
    pub open spec fn overlaps_vmem(self, vaddr: VAddr, frame: Frame) -> bool {
        exists|base: VAddr|
            {
                &&& #[trigger] self.mappings.contains_key(base)
                &&& VAddr::overlap(
                    base,
                    self.mappings.index(base).size.as_nat(),
                    vaddr,
                    frame.size.as_nat(),
                )
            }
    }

    /// Init state. Empty memory and no mappings.
    pub open spec fn init(self) -> bool {
        &&& self.mem === Map::empty()
        &&& self.mappings === Map::empty()
    }

    /// State transition - Read.
    pub open spec fn read(s1: Self, s2: Self, op: ReadOp, mapping: Option<(VAddr, Frame)>) -> bool {
        // Memory and mappings should be unchanged
        &&& s1.mappings === s2.mappings
        &&& s1.mem === s2.mem
        // Check mapping
        &&& match mapping {
            Some((base, frame)) => {
                // If `mapping` is `Some`, `s1.mappings` should contain it
                &&& s1.mappings.contains_pair(
                    base,
                    frame,
                )
                // `vaddr` should be in the virtual page marked by `base`
                &&& op.vaddr.between(
                    base,
                    base.offset(frame.size.as_nat()),
                )
                // Check frame attributes
                &&& if !frame.attr.readable || !frame.attr.user_accessible {
                    // If the frame is not readable or user accessible, the
                    // result should be `Err`
                    op.result is Err
                } else {
                    // Otherwise, the result should be `Ok`
                    &&& op.result is Ok
                    // The value should be the value in the memory at `vmem_word_idx`
                    &&& op.result.unwrap() === s1.mem[op.vaddr.word_idx()]
                }
            },
            None => {
                // If `mapping` is `None`, the memory domain should not contain `vmem_word_idx`
                &&& !s1.mem_domain_covered_by_mappings().contains(
                    op.vaddr.word_idx(),
                )
                // Result should be `Err`
                &&& op.result is Err
            },
        }
    }

    /// State transition - write.
    pub open spec fn write(
        s1: Self,
        s2: Self,
        op: WriteOp,
        mapping: Option<(VAddr, Frame)>,
    ) -> bool {
        // Mappings should be unchanged
        &&& s1.mappings === s2.mappings
        // Check mapping
        &&& match mapping {
            Some((base, frame)) => {
                // If `mapping` is `Some`, `s1.mappings` should contain it
                &&& s1.mappings.contains_pair(
                    base,
                    frame,
                )
                // `vaddr` should be in the virtual page marked by `base`
                &&& op.vaddr.between(
                    base,
                    base.offset(frame.size.as_nat()),
                )
                // Check frame attributes
                &&& if !frame.attr.writable || !frame.attr.user_accessible {
                    // If the frame is not writable or user accessible, the
                    // result should be `Err`
                    &&& op.result is Err
                    // Memory should be unchanged
                    &&& s1.mem === s2.mem
                } else {
                    // Otherwise, the result should be `Ok`
                    &&& op.result is Ok
                    // Memory should be updated at `vword_idx` with `value`
                    &&& s1.mem === s2.mem.insert(op.vaddr.word_idx(), op.value)
                }
            },
            None => {
                // If `mapping` is `None`, the memory domain should not contain `vword_idx`
                &&& !s1.mem_domain_covered_by_mappings().contains(
                    op.vaddr.word_idx(),
                )
                // And memory should be unchanged
                &&& s1.mem === s2.mem
                // Result should be `Err`
                &&& op.result is Err
            },
        }
    }

    /// State transtion - Map a virtual address to a frame.
    pub open spec fn map(s1: Self, s2: Self, op: MapOp) -> bool {
        // Base vaddr should align to frame size
        &&& op.vaddr.aligned(
            op.frame.size.as_nat(),
        )
        // Base paddr should align to frame size
        &&& op.frame.base.aligned(
            op.frame.size.as_nat(),
        )
        // Frame should not overlap with existing pmem
        &&& !s1.overlaps_pmem(op.frame)
        // Check vmem overlapping
        &&& if s1.overlaps_vmem(op.vaddr, op.frame) {
            // Mapping fails
            &&& op.result is Err
            // Memory and mappings should be unchanged
            &&& s1.mem === s2.mem
            &&& s1.mappings === s2.mappings
        } else {
            // Mapping succeeds
            &&& op.result is Ok
            // Update mappings
            &&& s1.mappings.insert(op.vaddr, op.frame)
                === s2.mappings
            // Memory domain should be updated
            &&& s2.mem.dom() === s2.mem_domain_covered_by_mappings()
        }
    }

    /// State transtion - Unmap a virtual address.
    pub open spec fn unmap(s1: Self, s2: Self, op: UnmapOp) -> bool {
        // Base vaddr should align to some valid frame size
        &&& {
            ||| op.vaddr.aligned(FrameSize::Size4K.as_nat())
            ||| op.vaddr.aligned(FrameSize::Size2M.as_nat())
            ||| op.vaddr.aligned(FrameSize::Size1G.as_nat())
        }
        // Check mapping
        &&& if s1.mappings.contains_key(op.vaddr) {
            // Unmapping succeeds
            &&& op.result is Ok
            // Update mappings
            &&& s1.mappings.remove(op.vaddr)
                === s2.mappings
            // Memory domain should be updated
            &&& s2.mem.dom() === s2.mem_domain_covered_by_mappings()
        } else {
            // Unmapping fails
            &&& op.result is Err
            // Memory and mappings should be unchanged
            &&& s1.mem === s2.mem
            &&& s1.mappings === s2.mappings
        }
    }
}

} // verus!
