//! Page table specification.
//!
//! This is the **proof target** of the page table implementation. If the page table implementation
//! satisfies this specification, along with the assumptions we make about the hardware and the
//! remaining OS, we can conclude that the whole system refines the low-level specification.
//! This module is not trusted (not a proof base).
use vstd::prelude::*;

use super::{
    addr::{PAddr, VAddr, VAddrExec, WORD_SIZE},
    frame::{Frame, FrameExec, FrameSize},
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

/// State transition specification.
impl PageTableState {
    /// map precondition.
    pub open spec fn map_pre(self, vaddr: VAddr, frame: Frame) -> bool {
        // Base vaddr should align to frame size
        &&& vaddr.aligned(
            frame.size.as_nat(),
        )
        // Base paddr should align to frame size
        &&& frame.base.aligned(
            frame.size.as_nat(),
        )
        // Frame should be within pmem
        &&& frame.base.offset(frame.size.as_nat()).0
            <= self.constants.pmem_size
        // Frame should not overlap with existing pmem
        &&& !self.overlaps_pmem(frame)
    }

    /// State transition - map a virtual address to a physical frame.
    pub open spec fn map(s1: Self, s2: Self, op: MapOp) -> bool {
        // Precondition
        &&& s1.map_pre(op.vaddr, op.frame)
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

    /// unmap precondition.
    pub open spec fn unmap_pre(self, vaddr: VAddr) -> bool {
        // Base vaddr should align to some valid frame size
        ||| vaddr.aligned(FrameSize::Size4K.as_nat())
        ||| vaddr.aligned(FrameSize::Size2M.as_nat())
        ||| vaddr.aligned(FrameSize::Size1G.as_nat())
    }

    /// State transition - unmap a virtual address.
    pub open spec fn unmap(s1: Self, s2: Self, op: UnmapOp) -> bool {
        // Precondition
        &&& s1.unmap_pre(op.vaddr)
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

    /// query precondition.
    pub open spec fn query_pre(self, vaddr: VAddr) -> bool {
        // Base vaddr should align to 8 bytes
        vaddr.aligned(WORD_SIZE)
    }

    /// State transition - page table query.
    pub open spec fn query(s1: Self, s2: Self, op: QueryOp) -> bool {
        // Precondition
        &&& s1.query_pre(op.vaddr)
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
}

/// Helper functions.
impl PageTableState {
    /// If `frame` overlaps with existing physical memory.
    pub open spec fn overlaps_pmem(self, frame: Frame) -> bool {
        exists|frame1: Frame|
            {
                &&& #[trigger] self.mappings.contains_value(frame1)
                &&& PAddr::overlap(
                    frame1.base,
                    frame1.size.as_nat(),
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

/// Page table must implement the `PageTableInterface` and satisfy the specification.
///
/// - `invariants` specifies the invariants that must be preserved after each operation.
/// - `view` abstracts the concrete page table as a `PageTableState`.
/// - `map` specifies the pre and post conditions for the `map` operation.
/// - `unmap` specifies the pre and post conditions for the `unmap` operation.
/// - `query` specifies the pre and post conditions for the `query` operation.
///
/// If a concrete implementation refines this specification (i.e. `impl PageTableInterface`),
/// along with the assumptions we make about the hardware and the remaining system, we can
/// conclude that the whole system refines the low-level specification, thus refines the
/// high-level specification.
pub trait PageTableInterface where Self: Sized {
    /// Specify the invariants that must be implied at initial state and preseved after each operation.
    spec fn invariants(self) -> bool;

    /// Specify the initial state.
    spec fn init(self) -> bool;

    /// Get abstract page table state.
    spec fn view(self) -> PageTableState;

    /// Prove that the initial state satisfies the invariants.
    proof fn init_implies_invariants(self)
        requires
            self.init(),
        ensures
            self.invariants(),
    ;

    /// **EXEC** Map a virtual address to a physical frame.
    ///
    /// Implementation must ensure the postconditions are satisfied.
    fn map(&mut self, vaddr: VAddrExec, frame: FrameExec) -> (result: Result<(), ()>)
        requires
            old(self).invariants(),
            old(self)@.map_pre(vaddr@, frame@),
        ensures
            self.invariants(),
            PageTableState::map(
                old(self)@,
                self@,
                MapOp { vaddr: vaddr@, frame: frame@, result },
            ),
    ;

    /// **EXEC** Unmap a virtual address.
    ///
    /// Implementation must ensure the postconditions are satisfied.
    fn unmap(&mut self, vaddr: VAddrExec) -> (result: Result<(), ()>)
        requires
            old(self).invariants(),
            old(self)@.unmap_pre(vaddr@),
        ensures
            self.invariants(),
            PageTableState::unmap(old(self)@, self@, UnmapOp { vaddr: vaddr@, result }),
    ;

    /// **EXEC** Query a virtual address, return the mapped physical frame.
    ///
    /// Implementation must ensure the postconditions are satisfied.
    fn query(&mut self, vaddr: VAddrExec) -> (result: Result<(VAddrExec, FrameExec), ()>)
        requires
            old(self).invariants(),
            old(self)@.query_pre(vaddr@),
        ensures
            self.invariants(),
            PageTableState::query(
                old(self)@,
                self@,
                QueryOp {
                    vaddr: vaddr@,
                    result: match result {
                        Ok((vaddr, frame)) => Ok((vaddr@, frame@)),
                        Err(()) => Err(()),
                    },
                },
            ),
    ;
}

} // verus!
