//! Page table interface.
//!
//! Concrete page table must implement this interface to satisfy the page table specification
//! defined in `spec::page_table`.
use vstd::prelude::*;

use crate::common::{
    addr::{PAddrExec, VAddrExec},
    arch::PTArchExec,
    frame::FrameExec,
    PagingResult,
};
use crate::spec::{
    memory::PageTableMemExec,
    page_table::{PTConstants, PageTableState},
};

verus! {

/// Page table config constants (exec mode).
#[derive(Clone)]
pub struct PTConstantsExec {
    /// Page table architecture.
    pub arch: PTArchExec,
    /// Physical memory lower bound.
    pub pmem_lb: PAddrExec,
    /// Physical memory upper bound.
    pub pmem_ub: PAddrExec,
}

impl PTConstantsExec {
    /// View as `PTConstants`
    pub open spec fn view(self) -> PTConstants {
        PTConstants { arch: self.arch@, pmem_lb: self.pmem_lb@, pmem_ub: self.pmem_ub@ }
    }
}

/// Concrete implementation must implement `PageTableInterface` to satisfy the specification.
///
/// - `invariants` specifies the invariants that must be preserved after each operation.
/// - `map` specifies the pre and post conditions for the `map` operation.
/// - `unmap` specifies the pre and post conditions for the `unmap` operation.
/// - `query` specifies the pre and post conditions for the `query` operation.
///
/// If a concrete implementation refines this specification (i.e. `impl PageTableInterface`),
/// along with the assumptions we make about the hardware and the remaining system, we can
/// conclude that the whole system refines the low-level specification, thus refines the
/// high-level specification.
pub trait PageTableInterface<M> where Self: Sized, M: PageTableMemExec {
    /// Invariants that must be implied at initial state and preseved after each operation.
    spec fn invariants(pt_mem: M, constants: PTConstantsExec) -> bool;

    /// Prove invariants are satified at the initial state.
    proof fn init_implies_invariants(pt_mem: M, constants: PTConstantsExec)
        requires
            pt_mem@.init(),
            pt_mem@.arch == constants@.arch,
        ensures
            Self::invariants(pt_mem, constants),
    ;

    /// Map a virtual address to a physical frame.
    ///
    /// Implementation must ensure the postconditions are satisfied.
    fn map(pt_mem: M, constants: PTConstantsExec, vbase: VAddrExec, frame: FrameExec) -> (res: (
        PagingResult,
        M,
    ))
        requires
            Self::invariants(pt_mem, constants),
            PageTableState::new(pt_mem@.interpret(), constants@).map_pre(vbase@, frame@),
        ensures
            Self::invariants(res.1, constants),
            PageTableState::map(
                PageTableState::new(pt_mem@.interpret(), constants@),
                PageTableState::new(res.1@.interpret(), constants@),
                vbase@,
                frame@,
                res.0,
            ),
    ;

    /// Unmap a virtual address.
    ///
    /// Implementation must ensure the postconditions are satisfied.
    fn unmap(pt_mem: M, constants: PTConstantsExec, vbase: VAddrExec) -> (res: (PagingResult, M))
        requires
            Self::invariants(pt_mem, constants),
            PageTableState::new(pt_mem@.interpret(), constants@).unmap_pre(vbase@),
        ensures
            Self::invariants(res.1, constants),
            PageTableState::unmap(
                PageTableState::new(pt_mem@.interpret(), constants@),
                PageTableState::new(res.1@.interpret(), constants@),
                vbase@,
                res.0,
            ),
    ;

    /// Query a virtual address, return the mapped physical frame.
    ///
    /// Implementation must ensure the postconditions are satisfied.
    fn query(pt_mem: M, constants: PTConstantsExec, vaddr: VAddrExec) -> (res: (
        PagingResult<(VAddrExec, FrameExec)>,
        M,
    ))
        requires
            Self::invariants(pt_mem, constants),
            PageTableState::new(pt_mem@.interpret(), constants@).query_pre(vaddr@),
        ensures
            Self::invariants(res.1, constants),
            PageTableState::query(
                PageTableState::new(pt_mem@.interpret(), constants@),
                PageTableState::new(res.1@.interpret(), constants@),
                vaddr@,
                match res.0 {
                    Ok((vaddr, frame)) => Ok((vaddr@, frame@)),
                    Err(()) => Err(()),
                },
            ),
    ;
}

} // verus!
