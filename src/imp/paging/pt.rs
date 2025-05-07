use std::marker::PhantomData;
use vstd::prelude::*;

use super::{addr::pte_index, pte::GenericPTE};
use crate::{
    imp::tree::PTTreeModel,
    spec::{
        addr::{PAddr, PAddrExec, VAddr, VAddrExec},
        arch::PTArch,
        frame::{FrameExec, FrameSize},
        pt_mem::PageTableMemExec,
    },
};

verus! {

/// Executable VMSAv8-64 page table using 4K granule.
pub struct PageTable<PTE: GenericPTE> {
    /// Page table memory, arch is `VMSAV8_4K_ARCH`
    pub pt_mem: PageTableMemExec,
    /// Phantom data.
    pub _phantom: PhantomData<PTE>,
}

impl<PTE> PageTable<PTE> where PTE: GenericPTE {
    /// Invariants that ensure the page table is well-formed.
    pub open spec fn invariants(self) -> bool {
        &&& self.pt_mem@.invariants()
        // Each table descriptor that can be accessed must point to a valid table
        &&& forall|base: PAddr, idx: nat|
            self.pt_mem@.accessible(base, idx) ==> {
                let table = self.pt_mem@.table(base);
                let pte = PTE::spec_from_u64(self.pt_mem@.read(base, idx));
                // PTE is valid and points to a table
                !self.pt_mem@.is_leaf(base) && pte.spec_valid() && !pte.spec_huge()
                    ==> self.pt_mem@.contains_table(pte.spec_addr())
            }
    }

    /// Page table architecture.
    pub open spec fn arch(self) -> PTArch {
        self.pt_mem@.arch
    }

    /// Get a page table entry with virtual address, terminate if reach an invalid entry or a huge page.
    pub open spec fn spec_get_entry(self, vaddr: VAddr) -> (PTE, nat) {
        self.spec_get_entry_recursive(vaddr, self.pt_mem@.root(), 0)
    }

    /// Recursive helper for `spec_get_entry`.
    pub open spec fn spec_get_entry_recursive(self, vaddr: VAddr, base: PAddr, level: nat) -> (
        PTE,
        nat,
    )
        decreases 4 - level,
    {
        let pte = PTE::spec_from_u64(
            self.pt_mem@.read(base, self.arch().pte_index_of_va(vaddr, 0)),
        );
        if pte.spec_valid() && !pte.spec_huge() && level < 3 {
            self.spec_get_entry_recursive(vaddr, pte.spec_addr(), level + 1)
        } else {
            (pte, level)
        }
    }

    /// Frame size at given level.
    pub fn frame_size(self, level: usize) -> FrameSize {
        if level == 0 {
            FrameSize::Size512G
        } else if level == 1 {
            FrameSize::Size1G
        } else if level == 2 {
            FrameSize::Size2M
        } else {
            FrameSize::Size4K
        }
    }

    /// Get a page table entry and its level with virtual address, terminate if reach an invalid entry
    /// or a huge page (block descriptor).
    ///
    /// The behavior is proved to be consistent with `spec_get_entry`.
    pub fn get_entry(&self, vaddr: VAddrExec) -> (res: (PTE, usize))
        requires
            self.invariants(),
        ensures
            (res.0, res.1 as nat) == self.spec_get_entry(vaddr@),
    {
        proof {
            // Ensures root table is accessible
            self.pt_mem@.lemma_contains_root();
            assert(self.pt_mem@.accessible(
                self.pt_mem@.root(),
                self.arch().pte_index_of_va(vaddr@, 0),
            ));
        }
        let p0e = PTE::from_u64(self.pt_mem.read(self.pt_mem.root(), pte_index(vaddr, 0)));
        if !p0e.valid() || p0e.huge() {
            return (p0e, 0);
        }
        let p1e = PTE::from_u64(self.pt_mem.read(p0e.addr(), pte_index(vaddr, 1)));
        if !p1e.valid() || p1e.huge() {
            return (p1e, 1);
        }
        let p2e = PTE::from_u64(self.pt_mem.read(p1e.addr(), pte_index(vaddr, 2)));
        if !p2e.valid() || p2e.huge() {
            return (p2e, 2);
        }
        let p3e = PTE::from_u64(self.pt_mem.read(p2e.addr(), pte_index(vaddr, 3)));
        (p3e, 3)
    }
    // fn new(pt_mem: PageTableMemExec) -> Self {
    //     Self { pt_mem }
    // }
    // fn get_entry(&self, vaddr: VAddrExec) -> PTE {
    // }
    // fn walk(
    //     &self,
    //     table: &[PTE],
    //     level: usize,
    //     start_vaddr: usize,
    //     limit: usize,
    //     func: &impl Fn(usize, usize, usize, &PTE),
    // ) {
    //     let mut n = 0;
    //     for (i, entry) in table.iter().enumerate() {
    //         let vaddr = start_vaddr + (i << (12 + (3 - level) * 9));
    //         if entry.is_present() {
    //             func(level, i, vaddr, entry);
    //             if level < 3 {
    //                 match next_table_mut(entry) {
    //                     Ok(entry) => self.walk(entry, level + 1, vaddr, limit, func),
    //                     Err(PagingError::MappedToHugePage) => {}
    //                     _ => unreachable!(),
    //                 }
    //             }
    //             n += 1;
    //             if n >= limit {
    //                 break;
    //             }
    //         }
    //     }
    // }
    // fn query(&self, vaddr: VAddrExec) -> Result<(PAddrExec, FrameExec)> {
    //     let (entry, size) = self.get_entry_mut(vaddr)?;
    //     if entry.is_unused() {
    //         return Err(());
    //     }
    //     let off = size.page_offset(vaddr.into());
    //     Ok((entry.addr() + off, entry.flags(), size))
    // }
    // fn alloc_intrm_table(&mut self) -> HvResult<PAddrExec> {
    //     let frame = Frame::new_zero()?;
    //     let paddr = frame.start_paddr();
    //     self.intrm_tables.push(frame);
    //     Ok(paddr)
    // }
    // fn _dealloc_intrm_table(&mut self, _paddr: PAddrExec) {}
    // fn get_entry_mut_or_create(&mut self, page: Page<VA>) -> PagingResult<&mut PTE> {
    //     let vaddr: usize = page.vaddr.into();
    //     let p3 = if self.inner.level == 4 {
    //         let p4 = table_of_mut::<PTE>(self.inner.root_paddr());
    //         let p4e = &mut p4[p4_index(vaddr)];
    //         next_table_mut_or_create(p4e, || self.alloc_intrm_table())?
    //     } else {
    //         table_of_mut::<PTE>(self.inner.root_paddr())
    //     };
    //     let p3e = &mut p3[p3_index(vaddr)];
    //     if page.size == FrameSize::Size1G {
    //         return Ok(p3e);
    //     }
    //     let p2 = next_table_mut_or_create(p3e, || self.alloc_intrm_table())?;
    //     let p2e = &mut p2[p2_index(vaddr)];
    //     if page.size == FrameSize::Size2M {
    //         return Ok(p2e);
    //     }
    //     let p1 = next_table_mut_or_create(p2e, || self.alloc_intrm_table())?;
    //     let p1e = &mut p1[p1_index(vaddr)];
    //     Ok(p1e)
    // }
    // fn map_frame(
    //     &mut self,
    //     vbase: VAddrExec,
    //     frame: FrameExec,
    // ) -> Result<PTE> {
    //     let entry: &mut PTE = self.get_entry_mut_or_create(page)?;
    //     if !entry.is_unused() {
    //         return Err(PagingError::AlreadyMapped);
    //     }
    //     entry.set_addr(page.size.align_down(paddr));
    //     entry.set_flags(flags, page.size.is_huge());
    //     Ok(entry)
    // }
    // fn unmap_page(&mut self, vaddr: VA) -> PagingResult<(PAddrExec, FrameSize)> {
    //     let (entry, size) = self.inner.get_entry_mut(vaddr)?;
    //     if entry.is_unused() {
    //         return Err(PagingError::NotMapped);
    //     }
    //     let paddr = entry.addr();
    //     entry.clear();
    //     Ok((paddr, size))
    // }
    // fn update(&mut self, vaddr: VA, paddr: PAddrExec, flags: MemFlags) -> PagingResult<FrameSize> {
    //     let (entry, size) = self.inner.get_entry_mut(vaddr)?;
    //     entry.set_addr(paddr);
    //     entry.set_flags(flags, size.is_huge());
    //     Ok(size)
    // }
    // fn map(&mut self, region: &MemoryRegion<VA>) -> HvResult {
    //     assert!(
    //         is_aligned(region.start.into()),
    //         "region.start = {:#x?}",
    //         region.start.into()
    //     );
    //     assert!(is_aligned(region.size), "region.size = {:#x?}", region.size);
    //     trace!(
    //         "create mapping in {}: {:#x?}",
    //         core::any::type_name::<Self>(),
    //         region
    //     );
    //     let _lock = self.clonee_lock.lock();
    //     let mut vaddr = region.start.into();
    //     let mut size = region.size;
    //     while size > 0 {
    //         let paddr = region.mapper.map_fn(vaddr);
    //         let page_size = if FrameSize::Size1G.is_aligned(vaddr)
    //             && FrameSize::Size1G.is_aligned(paddr)
    //             && size >= FrameSize::Size1G as usize
    //             && !region.flags.contains(MemFlags::NO_HUGEPAGES)
    //         {
    //             FrameSize::Size1G
    //         } else if FrameSize::Size2M.is_aligned(vaddr)
    //             && FrameSize::Size2M.is_aligned(paddr)
    //             && size >= FrameSize::Size2M as usize
    //             && !region.flags.contains(MemFlags::NO_HUGEPAGES)
    //         {
    //             FrameSize::Size2M
    //         } else {
    //             FrameSize::Size4K
    //         };
    //         let page = Page::new_aligned(vaddr.into(), page_size);
    //         self.inner
    //             .map_page(page, paddr, region.flags)
    //             .map_err(|e: PagingError| {
    //                 error!(
    //                     "failed to map page: {:#x?}({:?}) -> {:#x?}, {:?}",
    //                     vaddr, page_size, paddr, e
    //                 );
    //                 e
    //             })?;
    //         vaddr += page_size as usize;
    //         size -= page_size as usize;
    //     }
    //     Ok(())
    // }
    // fn unmap(&mut self, region: &MemoryRegion<VA>) -> HvResult {
    //     trace!(
    //         "destroy mapping in {}: {:#x?}",
    //         core::any::type_name::<Self>(),
    //         region
    //     );
    //     let _lock = self.clonee_lock.lock();
    //     let mut vaddr = region.start.into();
    //     let mut size = region.size;
    //     while size > 0 {
    //         let (_, page_size) = self.inner.unmap_page(vaddr.into()).map_err(|e| {
    //             error!("failed to unmap page: {:#x?}, {:?}", vaddr, e);
    //             e
    //         })?;
    //         if !page_size.is_aligned(vaddr) {
    //             error!("error vaddr={:#x?}", vaddr);
    //             loop {}
    //         }
    //         assert!(page_size.is_aligned(vaddr));
    //         assert!(page_size as usize <= size);
    //         vaddr += page_size as usize;
    //         size -= page_size as usize;
    //     }
    //     Ok(())
    // }

}

// fn table_of<'a, E>(paddr: PAddrExec) -> &'a [E] {
//     let ptr = paddr as *const E;
//     unsafe { slice::from_raw_parts(ptr, ENTRY_COUNT) }
// }
// fn table_of_mut<'a, E>(paddr: PAddrExec) -> &'a mut [E] {
//     let ptr = paddr as *mut E;
//     unsafe { slice::from_raw_parts_mut(ptr, ENTRY_COUNT) }
// }
// fn next_table_mut<'a, E: GenericPTE>(entry: &E) -> PagingResult<&'a mut [E]> {
//     if !entry.is_present() {
//         Err(PagingError::NotMapped)
//     } else if entry.is_huge() {
//         Err(PagingError::MappedToHugePage)
//     } else {
//         Ok(table_of_mut(entry.addr()))
//     }
// }
// fn next_table_mut_or_create<'a, E: GenericPTE>(
//     entry: &mut E,
//     mut allocator: impl FnMut() -> HvResult<PAddrExec>,
// ) -> PagingResult<&'a mut [E]> {
//     if entry.is_unused() {
//         let paddr = allocator().map_err(|_| PagingError::NoMemory)?;
//         entry.set_table(paddr);
//         Ok(table_of_mut(paddr))
//     } else {
//         next_table_mut(entry)
//     }
// }
} // verus!
