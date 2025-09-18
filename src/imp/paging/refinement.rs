//! Implementation refinement proof.
use core::marker::PhantomData;
use vstd::prelude::*;

use super::pt_exec::PageTableExec;
use crate::{
    common::{
        addr::{PAddr, VAddrExec},
        frame::FrameExec,
        pte::{ExecPTE, GhostPTE},
        PagingResult,
    },
    imp::interface::{PTConstantsExec, PageTableInterface},
    spec::memory::PageTableMemExec,
};

verus! {

/// A wrapper for `PageTable` that implements `PageTableInterface`.
///
/// Implementing `PageTableInterface` ensures the page table implementation satisfies the
/// interface specifications, along with the assumptions made about the hardware and the
/// remaining system, we can complete the proof of the paging system.
pub struct PageTableImpl<M: PageTableMemExec, G: GhostPTE, E: ExecPTE<G>>(PhantomData<(M, G, E)>);

impl<M, G, E> PageTableInterface<M> for PageTableImpl<M, G, E> where
    M: PageTableMemExec,
    G: GhostPTE,
    E: ExecPTE<G>,
 {
    open spec fn invariants(pt_mem: M, constants: PTConstantsExec) -> bool {
        PageTableExec::<M, G, E> { pt_mem, constants, _phantom: PhantomData }@.invariants()
    }

    proof fn init_implies_invariants(pt_mem: M, constants: PTConstantsExec) {
        broadcast use crate::common::pte::group_pte_lemmas;

        pt_mem.view().lemma_init_implies_invariants();
        let pt = PageTableExec::<M, G, E> { pt_mem, constants, _phantom: PhantomData };
        assert forall|base: PAddr, idx: nat| pt.pt_mem@.accessible(base, idx) implies {
            let pt_mem = pt.pt_mem@;
            let table = pt_mem.table(base);
            let pte = G::from_u64(pt_mem.read(base, idx));
            !pte.valid()
        } by {
            assert(base == pt_mem@.root());
            assert(pt_mem@.table_view(base) == seq![0u64; pt_mem@.arch.entry_count(0)]);
            assert(pt_mem@.read(base, idx) == 0);
        }
    }

    fn map(pt_mem: M, constants: PTConstantsExec, vbase: VAddrExec, frame: FrameExec) -> (res: (
        PagingResult,
        M,
    )) {
        let mut pt = PageTableExec::<M, G, E>::new(pt_mem, constants);
        proof {
            assert(pt@.invariants());
            pt@.model_consistent_with_hardware();
            pt@.lemma_view_implies_invariants();
            pt@@.map_refinement(vbase@, frame@);
        }
        let res = pt.map(vbase, frame);
        proof {
            assert(pt@.invariants());
            pt@.model_consistent_with_hardware();
        }
        (res, pt.pt_mem)
    }

    fn unmap(pt_mem: M, constants: PTConstantsExec, vbase: VAddrExec) -> (res: (PagingResult, M)) {
        let mut pt = PageTableExec::<M, G, E>::new(pt_mem, constants);
        proof {
            assert(pt@.invariants());
            pt@.model_consistent_with_hardware();
            pt@.lemma_view_implies_invariants();
            pt@@.unmap_refinement(vbase@);
        }
        let res = pt.unmap(vbase);
        proof {
            assert(pt@.invariants());
            pt@.model_consistent_with_hardware();
        }
        (res, pt.pt_mem)
    }

    fn query(pt_mem: M, constants: PTConstantsExec, vaddr: VAddrExec) -> (res: (
        PagingResult<(VAddrExec, FrameExec)>,
        M,
    )) {
        let pt = PageTableExec::<M, G, E>::new(pt_mem, constants);
        proof {
            assert(pt@.invariants());
            pt@.model_consistent_with_hardware();
            pt@.lemma_view_implies_invariants();
            pt@@.query_refinement(vaddr@);
        }
        let res = pt.query(vaddr);
        (res, pt.pt_mem)
    }
}

} // verus!
