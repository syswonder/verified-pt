//! Implementation refinement proof.
use std::marker::PhantomData;
use vstd::prelude::*;

use super::{arch::VMSAV8_4K_ARCH, pt::PageTable, pte::GenericPTE};
use crate::{
    common::{
        addr::{PAddr, VAddrExec},
        frame::FrameExec,
        PagingResult,
    },
    spec::{
        interface::{PTConstantsExec, PageTableInterface},
        memory::PageTableMemExec,
    },
};

verus! {

/// A wrapper for `PageTable` that implements `PageTableInterface`.
///
/// Implementing `PageTableInterface` ensures the page table implementation satisfies the
/// interface specifications, along with the assumptions made about the hardware and the
/// remaining system, we can complete the proof of the paging system.
pub struct PageTableImpl<PTE: GenericPTE>(PhantomData<PTE>);

impl<PTE> PageTableInterface for PageTableImpl<PTE> where PTE: GenericPTE {
    open spec fn invariants(pt_mem: PageTableMemExec, constants: PTConstantsExec) -> bool {
        PageTable::<PTE> { pt_mem, constants, _phantom: PhantomData }.invariants()
    }

    proof fn init_implies_invariants(pt_mem: PageTableMemExec, constants: PTConstantsExec) {
        assume(pt_mem.arch@ == VMSAV8_4K_ARCH);
        pt_mem.view().lemma_init_implies_invariants();
        let pt = PageTable::<PTE> { pt_mem, constants, _phantom: PhantomData };
        assert forall|base: PAddr, idx: nat| pt.pt_mem@.accessible(base, idx) implies {
            let pt_mem = pt.pt_mem@;
            let table = pt_mem.table(base);
            let pte = PTE::spec_from_u64(pt_mem.read(base, idx));
            !pte.spec_valid()
        } by {
            assert(base == pt_mem@.root());
            assert(pt_mem@.table_view(base) == seq![0u64; pt_mem@.arch.entry_count(0)]);
            assert(pt_mem@.read(base, idx) == 0);
            // TODO: Add specification for `GenericPTE` to eliminate this assumption.
            assume(PTE::spec_from_u64(0).spec_valid() == false);
        }
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
