//! Implementation refinement proof.
use vstd::prelude::*;

use super::{arch::VMSAV8_4K_ARCH, pt::PageTable, pt_mem::PageTableMemExec, pte::GenericPTE};
use crate::{
    common::{
        addr::{PAddrExec, VAddrExec},
        frame::FrameExec,
        PagingResult,
    },
    spec::pt_spec::{PageTableInterface, PageTableState},
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
pub struct PageTableImpl<PTE: GenericPTE>(pub PageTable<PTE>);

impl<PTE> PageTableInterface for PageTableImpl<PTE> where PTE: GenericPTE {
    open spec fn view(self) -> PageTableState {
        self.0.view().view()
    }

    open spec fn invariants(self) -> bool {
        self.0.invariants()
    }

    fn new() -> (res: Self) {
        let pt_mem = PageTableMemExec::new_vmsav8_4k(ROOT_TABLE_ADDR);
        assert(pt_mem.arch@ == VMSAV8_4K_ARCH);
        let pt = PageTable::new(pt_mem, PMEM_LB, PMEM_UB);
        Self(pt)
    }

    fn map(&mut self, vbase: VAddrExec, frame: FrameExec) -> (res: PagingResult) {
        proof {
            old(self).0.lemma_view_implies_invariants();
            old(self).0.view().map_refinement(vbase@, frame@);
        }
        self.0.map(vbase, frame)
    }

    fn unmap(&mut self, vbase: VAddrExec) -> (res: PagingResult) {
        proof {
            old(self).0.lemma_view_implies_invariants();
            old(self).0.view().unmap_refinement(vbase@);
        }
        self.0.unmap(vbase)
    }

    fn query(&mut self, vaddr: VAddrExec) -> (res: PagingResult<(VAddrExec, FrameExec)>) {
        proof {
            old(self).0.lemma_view_implies_invariants();
            old(self).0.view().query_refinement(vaddr@);
        }
        self.0.query(vaddr)
    }
}

} // verus!
