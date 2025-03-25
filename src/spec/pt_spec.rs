//! Page table specification.
//!
//! This is the **proof target** of the page table implementation. If the page table implementation
//! satisfies this specification, along with the assumptions we make about the hardware and the
//! remaining OS, we can conclude that the whole system refines the low-level specification.
//!
//! This module is not trusted (not a proof base).
use vstd::prelude::*;

use super::{
    addr::{PAddr, PIdx, VAddr, VAddrExec, WORD_SIZE},
    arch::PTArch,
    frame::{Frame, FrameExec},
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
    /// Page table architecture,
    pub arch: PTArch,
    /// Physical memory lower bound.
    pub pmem_lb: PIdx,
    /// Physical memory upper bound.
    pub pmem_ub: PIdx,
}

/// State transition specification.
impl PageTableState {
    /// Init state.
    pub open spec fn init(self) -> bool {
        self.mappings === Map::empty()
    }

    /// Map precondition.
    pub open spec fn map_pre(self, base: VAddr, frame: Frame) -> bool {
        // Arch should support frame size
        &&& self.constants.arch.valid_frame_sizes().contains(
            frame.size,
        )
        // Base vaddr should align to frame size
        &&& base.aligned(
            frame.size.as_nat(),
        )
        // Base paddr should align to frame size
        &&& frame.base.aligned(
            frame.size.as_nat(),
        )
        // Frame should be within pmem
        &&& self.within_pmem(frame.base.idx())
        &&& self.within_pmem(
            frame.base.offset(frame.size.as_nat()).idx(),
        )
        // Frame should not overlap with existing pmem
        &&& !self.overlaps_pmem(frame)
    }

    /// State transition - map a virtual address to a physical frame.
    pub open spec fn map(
        s1: Self,
        s2: Self,
        base: VAddr,
        frame: Frame,
        res: Result<(), ()>,
    ) -> bool {
        &&& s1.constants == s2.constants
        // Precondition
        &&& s1.map_pre(base, frame)
        // Check vmem overlapping
        &&& if s1.overlaps_vmem(base, frame) {
            // Mapping fails
            &&& res is Err
            // Page table should not be updated
            &&& s1.mappings === s2.mappings
        } else {
            // Mapping succeeds
            &&& res is Ok
            // Update page table
            &&& s1.mappings.insert(base, frame) === s2.mappings
        }
    }

    /// Unmap precondition.
    pub open spec fn unmap_pre(self, base: VAddr) -> bool {
        // Base vaddr should align to leaf frame size
        &&& base.aligned(self.constants.arch.leaf_frame_size().as_nat())
    }

    /// State transition - unmap a virtual address.
    pub open spec fn unmap(s1: Self, s2: Self, base: VAddr, res: Result<(), ()>) -> bool {
        &&& s1.constants == s2.constants
        // Precondition
        &&& s1.unmap_pre(base)
        // Check page table
        &&& if s1.mappings.contains_key(base) {
            // Unmapping succeeds
            &&& res is Ok
            // Update page table
            &&& s1.mappings.remove(base) === s2.mappings
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
        res: Result<(VAddr, Frame), ()>,
    ) -> bool {
        &&& s1.constants == s2.constants
        // Precondition
        &&& s1.query_pre(vaddr)
        // Page table should not be updated
        &&& s1.mappings === s2.mappings
        // Check result
        &&& match res {
            Ok((base, frame)) => {
                // Page table must contain the mapping
                &&& s1.mappings.contains_pair(base, frame)
                &&& vaddr.within(base, frame.size.as_nat())
            },
            Err(_) => {
                // Page table should not contain any mapping for vaddr
                !exists|base, frame|
                    {
                        &&& #[trigger] s1.mappings.contains_pair(base, frame)
                        &&& vaddr.within(base, frame.size.as_nat())
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

    /// If `pidx` is within physical memory.
    pub open spec fn within_pmem(self, pidx: PIdx) -> bool {
        self.constants.pmem_lb.0 <= pidx.0 < self.constants.pmem_ub.0
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
    /// Get abstract page table state.
    spec fn view(self) -> PageTableState;

    /// Specify the invariants that must be implied at initial state and preseved
    /// after each operation.
    spec fn invariants(self) -> bool;

    /// The assumptions we made about the hardware and the remaining system implies
    /// `self@.init()` at the system initialization.
    ///
    /// Implementation must prove that the invariants are satisfied at this initial state.
    proof fn init_implies_invariants(self)
        requires
            self@.init(),
        ensures
            self.invariants(),
    ;

    /// **EXEC** Map a virtual address to a physical frame.
    ///
    /// Implementation must ensure the postconditions are satisfied.
    fn map(&mut self, vaddr: VAddrExec, frame: FrameExec) -> (res: Result<(), ()>)
        requires
            old(self).invariants(),
            old(self)@.map_pre(vaddr@, frame@),
        ensures
            self.invariants(),
            PageTableState::map(old(self)@, self@, vaddr@, frame@, res),
    ;

    /// **EXEC** Unmap a virtual address.
    ///
    /// Implementation must ensure the postconditions are satisfied.
    fn unmap(&mut self, vaddr: VAddrExec) -> (res: Result<(), ()>)
        requires
            old(self).invariants(),
            old(self)@.unmap_pre(vaddr@),
        ensures
            self.invariants(),
            PageTableState::unmap(old(self)@, self@, vaddr@, res),
    ;

    /// **EXEC** Query a virtual address, return the mapped physical frame.
    ///
    /// Implementation must ensure the postconditions are satisfied.
    fn query(&mut self, vaddr: VAddrExec) -> (res: Result<(VAddrExec, FrameExec), ()>)
        requires
            old(self).invariants(),
            old(self)@.query_pre(vaddr@),
        ensures
            self.invariants(),
            PageTableState::query(
                old(self)@,
                self@,
                vaddr@,
                match res {
                    Ok((vaddr, frame)) => Ok((vaddr@, frame@)),
                    Err(()) => Err(()),
                },
            ),
    ;
}

} // verus!
