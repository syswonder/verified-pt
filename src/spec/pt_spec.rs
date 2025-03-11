//! Page table specification.
//!
//! This is the **proof target** of the page table implementation. If the page table implementation
//! satisfies this specification, along with the assumptions we make about the hardware and the
//! remaining OS, we can conclude that the whole system refines the low-level specification.
//! This module is not trusted (not a proof base).
use vstd::prelude::*;

use super::{
    addr::{PAddr, VAddr, WORD_SIZE},
    frame::{Frame, FrameSize},
    op::{MapOp, QueryOp, UnmapOp},
};

verus! {

/// Abstract state managed by the page table.
pub struct PageTableState {
    /// Mappings from virtual address to physical frames.
    pub mappings: Map<VAddr, Frame>,
    /// Page table.
    pub constants: PTConstants,
}

/// Page table config constants.
pub struct PTConstants {
    /// Physical memory size (in bytes).
    pub pmem_size: nat,
}

impl PageTableState {
    /// State transition - map a virtual address to a physical frame.
    pub open spec fn pt_map(s1: Self, s2: Self, op: MapOp) -> bool {
        // Base vaddr should align to frame size
        &&& op.vaddr.aligned(
            op.frame.size.as_nat(),
        )
        // Base paddr should align to frame size
        &&& op.frame.base.aligned(
            op.frame.size.as_nat(),
        )
        // Frame should be within pmem
        &&& op.frame.base.offset(op.frame.size.as_nat()).0
            <= s1.constants.pmem_size
        // Frame should not overlap with existing pmem
        &&& !s1.overlaps_pmem(op.frame)
        // Check vmem overlapping
        &&& if s1.overlaps_vmem(op.vaddr, op.frame) {
            // Mapping fails
            &&& op.result is Err
            // Page table should not be updated
            &&& s1.mappings === s2.mappings
        } else {
            // Mapping succeeds
            &&& op.result is Ok
            // Update page table
            &&& s1.mappings.insert(op.vaddr, op.frame) === s2.mappings
        }
    }

    /// State transition - unmap a virtual address.
    pub open spec fn pt_unmap(s1: Self, s2: Self, op: UnmapOp) -> bool {
        // Base vaddr should align to some valid frame size
        &&& {
            ||| op.vaddr.aligned(FrameSize::Size4K.as_nat())
            ||| op.vaddr.aligned(FrameSize::Size2M.as_nat())
            ||| op.vaddr.aligned(FrameSize::Size1G.as_nat())
        }
        // Check page table
        &&& if s1.mappings.contains_key(op.vaddr) {
            // Unmapping succeeds
            &&& op.result is Ok
            // Update page table
            &&& s1.mappings.remove(op.vaddr) === s2.mappings
        } else {
            // Unmapping fails
            &&& op.result is Err
            // Page table should not be updated
            &&& s1.mappings === s2.mappings
        }
    }

    /// State transition - page table query.
    pub open spec fn pt_query(s1: Self, s2: Self, op: QueryOp) -> bool {
        // Base vaddr should align to 8 bytes
        &&& op.vaddr.aligned(
            WORD_SIZE,
        )
        // Page table should not be updated
        &&& s1.mappings === s2.mappings
        // Check result
        &&& match op.result {
            Ok((base, frame)) => {
                // Page table must contain the mapping
                &&& s1.mappings.contains_pair(base, frame)
                &&& op.vaddr.within(base, frame.size.as_nat())
            },
            Err(_) => {
                // Page table should not contain any mapping for op.vaddr
                !exists|base, frame|
                    {
                        &&& #[trigger] s1.mappings.contains_pair(base, frame)
                        &&& op.vaddr.within(base, frame.size.as_nat())
                    }
            },
        }
    }

    /// If `frame` overlaps with existing physical memory.
    pub open spec fn overlaps_pmem(self, frame: Frame) -> bool {
        exists|base: VAddr|
            {
                &&& #[trigger] self.mappings.contains_key(base)
                &&& PAddr::overlap(
                    self.mappings[base].base,
                    self.mappings[base].size.as_nat(),
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
                    self.mappings[base].size.as_nat(),
                    vaddr,
                    frame.size.as_nat(),
                )
            }
    }
}

} // verus!
