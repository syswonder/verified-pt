//! Implementation refinement proof.
use std::marker::PhantomData;

use vstd::prelude::*;

use super::{pt::PageTable, pte::GenericPTE};
use crate::{
    common::{
        addr::{PAddrExec, VAddrExec},
        frame::FrameExec,
        PagingResult,
    },
    spec::{
        interface::{PTConstantsExec, PageTableInterface},
        memory::PageTableMemExec,
    },
};

verus! {

/// Physical mempry lower bound.
pub const PMEM_LB: PAddrExec = PAddrExec(0x1000_0000);

/// Physical memory upper bound.
pub const PMEM_UB: PAddrExec = PAddrExec(0x2000_0000);

/// Root page table address.
pub const ROOT_TABLE_ADDR: PAddrExec = PAddrExec(0x2000_0000);

/// A wrapper for `PageTable` that implements `PageTableInterface`.
///
/// Implementing `PageTableInterface` ensures the page table implementation satisfies the
/// interface specifications, along with the assumptions we made about the hardware and the
/// remaining system, we can complete the proof of the paging system.
pub struct PageTableImpl<PTE: GenericPTE>(PhantomData<PTE>);

impl<PTE> PageTableInterface for PageTableImpl<PTE> where PTE: GenericPTE {
    open spec fn invariants(pt_mem: PageTableMemExec, constants: PTConstantsExec) -> bool {
        PageTable::<PTE> {
            pt_mem,
            constants,
            _phantom: PhantomData,
        }.invariants()
    }

    fn map(
        pt_mem: PageTableMemExec,
        constants: PTConstantsExec,
        vbase: VAddrExec,
        frame: FrameExec,
    ) -> (res: (PagingResult, PageTableMemExec)) {
        let mut pt = PageTable::<PTE>::new(pt_mem, constants);
        proof {
            assert(pt.invariants());
            pt.lemma_view_consistent_with_interpret();
            pt.lemma_view_implies_invariants();
            pt.view().map_refinement(vbase@, frame@);
        }
        let res = pt.map(vbase, frame);
        proof {
            assert(pt.invariants());
            pt.lemma_view_consistent_with_interpret();
        }
        (res, pt.pt_mem)
    }

    fn unmap(pt_mem: PageTableMemExec, constants: PTConstantsExec, vbase: VAddrExec) -> (res: (
        PagingResult,
        PageTableMemExec,
    )) {
        let mut pt = PageTable::<PTE>::new(pt_mem, constants);
        proof {
            assert(pt.invariants());
            pt.lemma_view_consistent_with_interpret();
            pt.lemma_view_implies_invariants();
            pt.view().unmap_refinement(vbase@);
        }
        let res = pt.unmap(vbase);
        proof {
            assert(pt.invariants());
            pt.lemma_view_consistent_with_interpret();
        }
        (res, pt.pt_mem)
    }

    fn query(pt_mem: PageTableMemExec, constants: PTConstantsExec, vaddr: VAddrExec) -> (res: (
        PagingResult<(VAddrExec, FrameExec)>,
        PageTableMemExec,
    )) {
        let mut pt = PageTable::<PTE>::new(pt_mem, constants);
        proof {
            assert(pt.invariants());
            pt.lemma_view_consistent_with_interpret();
            pt.lemma_view_implies_invariants();
            pt.view().query_refinement(vaddr@);
        }
        let res = pt.query(vaddr);
        (res, pt.pt_mem)
    }
}

} // verus!
