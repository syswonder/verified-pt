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

use super::{
    mem::{Frame, FrameSize, MapOp, UnmapOp},
    os::OSMemoryState,
    PAddr, VAddr,
};

verus! {

impl OSMemoryState {
    /// If `frame` overlaps with existing physical memory.
    pub open spec fn overlaps_pmem(self, frame: Frame) -> bool {
        exists|base: VAddr|
            {
                &&& #[trigger] self.interpret_pt_mem().contains_key(base)
                &&& PAddr::overlap(
                    self.interpret_pt_mem().index(base).base,
                    self.interpret_pt_mem().index(base).size.as_nat(),
                    frame.base,
                    frame.size.as_nat(),
                )
            }
    }

    /// If mapping `(vaddr, frame)` overlaps with existing virtual memory.
    pub open spec fn overlaps_vmem(self, vaddr: VAddr, frame: Frame) -> bool {
        exists|base: VAddr|
            {
                &&& #[trigger] self.interpret_pt_mem().contains_key(base)
                &&& VAddr::overlap(
                    base,
                    self.interpret_pt_mem().index(base).size.as_nat(),
                    vaddr,
                    frame.size.as_nat(),
                )
            }
    }

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
        // Frame should not overlap with existing pmem
        &&& !s1.overlaps_pmem(op.frame)
        // Check vmem overlapping
        &&& if s1.overlaps_vmem(op.vaddr, op.frame) {
            // Mapping fails
            &&& op.result is Err
            // Page table should not be updated
            &&& s1.interpret_pt_mem() === s2.interpret_pt_mem()
        } else {
            // Mapping succeeds
            &&& op.result is Ok
            // Update page table
            &&& s1.interpret_pt_mem().insert(op.vaddr, op.frame) === s2.interpret_pt_mem()
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
        &&& if s1.interpret_pt_mem().contains_key(op.vaddr) {
            // Unmapping succeeds
            &&& op.result is Ok
            // Update page table
            &&& s1.interpret_pt_mem().remove(op.vaddr) === s2.interpret_pt_mem()
        } else {
            // Unmapping fails
            &&& op.result is Err
            // Page table should not be updated
            &&& s1.interpret_pt_mem() === s2.interpret_pt_mem()
        }
    }
}

} // verus!
