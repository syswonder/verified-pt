//! Page table specification.
//!
//! This is the **proof target** of the page table implementation. If the page table implementation
//! satisfies this specification, along with the assumptions we make about the hardware and the
//! remaining OS, we can conclude that the whole system refines the low-level specification.
//!
//! This module is not trusted (not a proof base).
use vstd::prelude::*;

use crate::common::{
    addr::{PAddr, VAddr, WORD_SIZE},
    arch::PTArch,
    frame::Frame,
    PagingResult,
};

verus! {

/// Abstract state managed by the page table.
pub struct PageTableState {
    /// Mappings from virtual address to physical frames.
    pub mappings: Map<VAddr, Frame>,
    /// Page table constants.
    pub constants: PTConstants,
}

/// Page table config constants.
pub struct PTConstants {
    /// Page table architecture.
    pub arch: PTArch,
    /// Physical memory lower bound.
    pub pmem_lb: PAddr,
    /// Physical memory upper bound.
    pub pmem_ub: PAddr,
}

/// State transition specification.
impl PageTableState {
    /// Init state.
    ///
    /// `LowlevelState::init()` implies `PageTableState::init()`.
    pub open spec fn init(self) -> bool {
        &&& self.mappings === Map::empty()
        &&& self.constants.arch.valid()
    }

    /// Map precondition.
    pub open spec fn map_pre(self, vbase: VAddr, frame: Frame) -> bool {
        // Arch should support frame size
        &&& self.constants.arch.is_valid_frame_size(
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
        &&& frame.base.0 >= self.constants.pmem_lb.0
        &&& frame.base.0 + frame.size.as_nat()
            <= self.constants.pmem_ub.0
        // Frame should not overlap with existing pmem
        &&& !self.overlaps_pmem(frame)
    }

    /// State transition - map a virtual address to a physical frame.
    pub open spec fn map(
        s1: Self,
        s2: Self,
        vbase: VAddr,
        frame: Frame,
        res: PagingResult,
    ) -> bool {
        &&& s1.constants == s2.constants
        // Precondition
        &&& s1.map_pre(vbase, frame)
        // Check vmem overlapping
        &&& if s1.overlaps_vmem(vbase, frame) {
            // Mapping fails
            &&& res is Err
            // Page table should not be updated
            &&& s1.mappings === s2.mappings
        } else {
            // Mapping succeeds
            &&& res is Ok
            // Update page table
            &&& s1.mappings.insert(vbase, frame) === s2.mappings
        }
    }

    /// Unmap precondition.
    pub open spec fn unmap_pre(self, vbase: VAddr) -> bool {
        // Base vaddr should align to leaf frame size
        vbase.aligned(self.constants.arch.leaf_frame_size().as_nat())
    }

    /// State transition - unmap a virtual address.
    pub open spec fn unmap(s1: Self, s2: Self, vbase: VAddr, res: PagingResult) -> bool {
        &&& s1.constants == s2.constants
        // Precondition
        &&& s1.unmap_pre(vbase)
        // Check page table
        &&& if s1.mappings.contains_key(vbase) {
            // Unmapping succeeds
            &&& res is Ok
            // Update page table
            &&& s1.mappings.remove(vbase) === s2.mappings
        } else {
            // Unmapping fails
            &&& res is Err
            // Page table should not be updated
            &&& s1.mappings === s2.mappings
        }
    }

    /// Query precondition.
    pub open spec fn query_pre(self, vaddr: VAddr) -> bool {
        // Base vaddr should align to 8 bytes
        vaddr.aligned(WORD_SIZE)
    }

    /// State transition - page table query.
    pub open spec fn query(
        s1: Self,
        s2: Self,
        vaddr: VAddr,
        res: PagingResult<(VAddr, Frame)>,
    ) -> bool {
        &&& s1.constants == s2.constants
        // Precondition
        &&& s1.query_pre(vaddr)
        // Page table should not be updated
        &&& s1.mappings === s2.mappings
        // Check result
        &&& if s1.has_mapping_for(vaddr) {
            // Query succeeds
            &&& res is Ok
            &&& res.unwrap() == s1.mapping_for(vaddr)
        } else {
            // Query fails
            &&& res is Err
        }
    }
}

/// Helper functions.
impl PageTableState {
    /// Construct a page table state.
    pub open spec fn new(mappings: Map<VAddr, Frame>, constants: PTConstants) -> Self {
        Self { mappings, constants }
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
}

} // verus!
