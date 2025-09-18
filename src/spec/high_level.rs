//! High-level state machine & high-level specifications.
//!
//! This is the high-level abstraction of the memory management module, which gives
//! a completely abstract view of the memory state with all implementation details removed.
//!
//! To prove an implementation’s correctness we need to ask what we mean
//! by correctness. The application specification is a state machine encoding our
//! answer to that question.
//!
//! This specification represents the proof target. Our implementation running
//! in the intended environment should refine it. This is demonstrated in part
//! by the proof that the low-level state machine refines this specification.
use vstd::prelude::*;

use crate::common::{
    addr::{PAddr, PIdx, VAddr, VIdx},
    arch::PTArch,
    frame::Frame,
    MemoryResult, PagingResult,
};

verus! {

/// High-level (abstract) memory state.
pub struct HighLevelState {
    /// 8-byte-indexed virtual memory.
    ///
    /// Use index rather than address. Addresses that are not aligned to 8-byte boundaries
    /// should not be used to access a value, while indexes don't face this issue.
    pub mem: Map<VIdx, u64>,
    /// Mappings from virtual address to physical frames.
    ///
    /// The key must be the base address of a virtual page i.e. range [`key`, `key + frame.size`)
    /// must be mapped to the same physical frame.
    pub mappings: Map<VAddr, Frame>,
    /// Constants.
    pub constants: HighLevelConstants,
}

/// Constants for the high-level state.
pub struct HighLevelConstants {
    /// Page table architecture.
    pub arch: PTArch,
    /// Physical memory lower bound.
    pub pmem_lb: PIdx,
    /// Physical memory upper bound.
    pub pmem_ub: PIdx,
}

/// State transition specifications.
impl HighLevelState {
    /// Init state. Empty memory and no mappings.
    pub open spec fn init(self) -> bool {
        &&& self.mem === Map::empty()
        &&& self.mappings === Map::empty()
        &&& self.constants.arch.valid()
    }

    /// State transition - Read.
    pub open spec fn read(s1: Self, s2: Self, vaddr: VAddr, res: MemoryResult<u64>) -> bool {
        &&& s1.constants === s2.constants
        // vaddr should align to 8 bytes
        &&& vaddr.aligned(8)
        // Memory and mappings should not be updated
        &&& s1.mappings === s2.mappings
        &&& s1.mem === s2.mem
        // Check mapping
        &&& if s1.has_mapping_for(vaddr) {
            let (base, frame) = s1.mapping_for(vaddr);
            // Check frame attributes
            if s1.within_pmem(vaddr.map(base, frame.base).idx()) && frame.attr.readable
                && frame.attr.user_accessible {
                &&& res is Ok
                // The value should be the value in the memory at `vidx`
                &&& res->Ok_0 === s1.mem[vaddr.idx()]
            } else {
                res is PageFault
            }
        } else {
            res is PageFault
        }
    }

    /// State transition - write.
    pub open spec fn write(
        s1: Self,
        s2: Self,
        vaddr: VAddr,
        value: u64,
        res: MemoryResult<()>,
    ) -> bool {
        &&& s1.constants === s2.constants
        // vaddr should align to 8 bytes
        &&& vaddr.aligned(8)
        // Mappings should not be updated
        &&& s1.mappings === s2.mappings
        // Check mapping
        &&& if s1.has_mapping_for(vaddr) {
            let (base, frame) = s1.mapping_for(vaddr);
            // Check frame attributes
            if s1.within_pmem(vaddr.map(base, frame.base).idx()) && frame.attr.writable
                && frame.attr.user_accessible {
                &&& res is Ok
                // Memory should be updated at `vidx` with `value`
                &&& s2.mem === s1.mem.insert(vaddr.idx(), value)
            } else {
                &&& res is PageFault
                // Memory should not be updated
                &&& s1.mem === s2.mem
            }
        } else {
            &&& res is PageFault
            // Memory should not be updated
            &&& s1.mem === s2.mem
        }
    }

    /// State transtion - Map a virtual address to a frame.
    pub open spec fn map(
        s1: Self,
        s2: Self,
        vbase: VAddr,
        frame: Frame,
        res: PagingResult,
    ) -> bool {
        &&& s1.constants
            === s2.constants
        // Arch should support frame size
        &&& s1.constants.arch.is_valid_frame_size(
            frame.size,
        )
        // Base vaddr should align to frame size
        &&& vbase.aligned(
            frame.size.as_nat(),
        )
        // Base paddr should align to frame size
        &&& frame.base.aligned(
            frame.size.as_nat(),
        )
        // Frame should be within pmem
        &&& frame.base.idx().0 >= s1.constants.pmem_lb.0
        &&& frame.base.offset(frame.size.as_nat()).idx().0
            <= s1.constants.pmem_ub.0
        // Frame should not overlap with existing pmem
        &&& !s1.overlaps_pmem(frame)
        // Check vmem overlapping
        &&& if s1.overlaps_vmem(vbase, frame) {
            &&& res is Err
            // Memory and mappings should not be updated
            &&& s1.mem === s2.mem
            &&& s1.mappings === s2.mappings
        } else {
            &&& res is Ok
            // Update mappings
            &&& s1.mappings.insert(vbase, frame)
                === s2.mappings
            // Memory domain should be updated
            &&& s2.mem.dom() === s2.mem_domain_covered_by_mappings()
        }
    }

    /// State transtion - Unmap a virtual address.
    pub open spec fn unmap(s1: Self, s2: Self, vbase: VAddr, res: PagingResult) -> bool {
        &&& s1.constants
            === s2.constants
        // Base vaddr should align to leaf frame size
        &&& vbase.aligned(
            s1.constants.arch.leaf_frame_size().as_nat(),
        )
        // Check mapping
        &&& if s1.mappings.contains_key(vbase) {
            &&& res is Ok
            // Update mappings
            &&& s1.mappings.remove(vbase)
                === s2.mappings
            // Memory domain should be updated
            &&& s2.mem.dom() === s2.mem_domain_covered_by_mappings()
        } else {
            &&& res is Err
            // Memory and mappings should not be updated
            &&& s1.mem === s2.mem
            &&& s1.mappings === s2.mappings
        }
    }

    /// State transition - Page table query.
    pub open spec fn query(
        s1: Self,
        s2: Self,
        vaddr: VAddr,
        res: PagingResult<(VAddr, Frame)>,
    ) -> bool {
        &&& s1.constants
            === s2.constants
        // Memory and mappings should not be updated
        &&& s1.mem === s2.mem
        &&& s1.mappings === s2.mappings
        &&& if s1.has_mapping_for(vaddr) {
            // Query succeeds
            &&& res is Ok
            &&& res.unwrap() == s1.mapping_for(vaddr)
        } else {
            // Query fails
            &&& res is Err
        }
    }

    /// State transition - Identity.
    pub open spec fn id(s1: Self, s2: Self) -> bool {
        s1 === s2
    }
}

/// Helper functions.
impl HighLevelState {
    /// Virtual memory domain covered by `self.mappings`.
    pub open spec fn mem_domain_covered_by_mappings(self) -> Set<VIdx> {
        Set::new(
            |vidx: VIdx|
                exists|vbase: VAddr, frame: Frame|
                    {
                        &&& #[trigger] self.mappings.contains_pair(vbase, frame)
                        &&& vidx.addr().within(vbase, frame.size.as_nat())
                    },
        )
    }

    /// If `frame` overlaps with existing physical memory.
    pub open spec fn overlaps_pmem(self, frame: Frame) -> bool {
        exists|frame2: Frame|
            {
                &&& #[trigger] self.mappings.contains_value(frame2)
                &&& PAddr::overlap(
                    frame2.base,
                    frame2.size.as_nat(),
                    frame.base,
                    frame.size.as_nat(),
                )
            }
    }

    /// If mapping `(vaddr, frame)` overlaps with existing virtual memory.
    pub open spec fn overlaps_vmem(self, vbase: VAddr, frame: Frame) -> bool {
        exists|vbase2: VAddr|
            {
                &&& #[trigger] self.mappings.contains_key(vbase2)
                &&& VAddr::overlap(
                    vbase2,
                    self.mappings[vbase2].size.as_nat(),
                    vbase,
                    frame.size.as_nat(),
                )
            }
    }

    /// If there exists a mapping for `vaddr`.
    pub open spec fn has_mapping_for(self, vaddr: VAddr) -> bool {
        exists|vbase: VAddr, frame: Frame|
            {
                &&& #[trigger] self.mappings.contains_pair(vbase, frame)
                &&& vaddr.within(vbase, frame.size.as_nat())
            }
    }

    /// Get the mapping for `vaddr`.
    pub open spec fn mapping_for(self, vaddr: VAddr) -> (VAddr, Frame)
        recommends
            self.has_mapping_for(vaddr),
    {
        choose|vbase: VAddr, frame: Frame|
            {
                &&& #[trigger] self.mappings.contains_pair(vbase, frame)
                &&& vaddr.within(vbase, frame.size.as_nat())
            }
    }

    /// If `pidx` is within physical memory.
    pub open spec fn within_pmem(self, pidx: PIdx) -> bool {
        self.constants.pmem_lb.0 <= pidx.0 < self.constants.pmem_ub.0
    }
}

} // verus!
