//! Executable page table implementation.
use std::marker::PhantomData;
use vstd::prelude::*;

use super::{addr::pte_index, pt_mem::PageTableMemExec, pte::GenericPTE};
use crate::{
    common::{
        addr::{PAddr, PAddrExec, VAddr, VAddrExec},
        arch::{PTArch, VMSAV8_4K_ARCH},
        frame::{Frame, FrameSize},
    },
    imp::tree::{
        model::PTTreeModel,
        node::{NodeEntry, PTConfig, PTTreeNode},
    },
};

verus! {

/// Executable 4-level page table implementation.
///
/// Only support VMSAv8-64 page table using 4K granule yet, but can be extended to other
/// architectures in future works.
pub struct PageTable<PTE: GenericPTE> {
    /// Page table memory, arch is `VMSAV8_4K_ARCH`
    pub pt_mem: PageTableMemExec,
    /// Phantom data.
    pub _phantom: PhantomData<PTE>,
    /// Physical memory lower bound.
    pub pmem_lb: PAddrExec,
    /// Physical memory upper bound.
    pub pmem_ub: PAddrExec,
}

impl<PTE> PageTable<PTE> where PTE: GenericPTE {
    /// Page table architecture.
    pub open spec fn arch(self) -> PTArch {
        self.pt_mem@.arch
    }

    /// Invariants that ensure the page table is well-formed.
    pub open spec fn invariants(self) -> bool {
        // Target architecture
        &&& self.arch() == VMSAV8_4K_ARCH
        // Page table memory invariants
        &&& self.pt_mem@.invariants()
        // Each table descriptor that can be accessed must point to a valid table
        &&& forall|base: PAddr, idx: nat|
            self.pt_mem@.accessible(base, idx) ==> {
                let pt_mem = self.pt_mem@;
                let table = pt_mem.table(base);
                let pte = PTE::spec_from_u64(pt_mem.read(base, idx));
                // If `base` is not a leaf table, `pte` is valid and points to a table...
                // then `pt_mem` contains the table, and the table level is one level higher than `base`
                ({
                    &&& table.level != self.arch().level_count()
                    &&& pte.spec_valid()
                    &&& !pte.spec_huge()
                }) ==> {
                    &&& pt_mem.contains_table(pte.spec_addr())
                    &&& pt_mem.table(pte.spec_addr()).level == pt_mem.table(base).level + 1
                }
            }
    }

    /// View as a page table tree model.
    pub open spec fn view(self) -> PTTreeModel
        recommends
            self.invariants(),
    {
        PTTreeModel { root: self.build_node(self.pt_mem@.root(), 0) }
    }

    /// Build a `PTTreeNode` for a sub-table
    pub open spec fn build_node(self, base: PAddr, level: nat) -> PTTreeNode
        recommends
            self.invariants(),
            self.pt_mem@.contains_table(base),
            level == self.pt_mem@.table(base).level,
            level < self.arch().level_count(),
        decreases self.arch().level_count() - level,
    {
        let arch = self.arch();
        let pt_mem = self.pt_mem.view();
        let table = pt_mem.table(base);
        // Construct entries for the node
        let entries = if level >= arch.level_count() - 1 {
            // Leaf table
            Seq::new(
                arch.entry_count(level),
                |i|
                    {
                        let pte = PTE::spec_from_u64(pt_mem.read(base, i as nat));
                        if pte.spec_valid() {
                            // Page descriptor
                            NodeEntry::Frame(
                                Frame {
                                    base: pte.spec_addr(),
                                    size: arch.frame_size(level),
                                    attr: pte.spec_attr(),
                                },
                            )
                        } else {
                            // Invalid entry
                            NodeEntry::Empty
                        }
                    },
            )
        } else {
            // Intermediate table
            Seq::new(
                arch.entry_count(level),
                |i|
                    {
                        let pte = PTE::spec_from_u64(pt_mem.read(base, i as nat));
                        if pte.spec_valid() {
                            if pte.spec_huge() {
                                // Block descriptor
                                NodeEntry::Frame(
                                    Frame {
                                        base: pte.spec_addr(),
                                        size: arch.frame_size(level),
                                        attr: pte.spec_attr(),
                                    },
                                )
                            } else {
                                // Table descriptor, recursively build node
                                NodeEntry::Node(self.build_node(pte.spec_addr(), level + 1))
                            }
                        } else {
                            // Invalid entry
                            NodeEntry::Empty
                        }
                    },
            )
        };
        PTTreeNode {
            config: PTConfig { arch, pmem_lb: self.pmem_lb@, pmem_ub: self.pmem_ub@ },
            level,
            entries,
        }
    }

    /// Get a page table entry and its level with virtual address, terminate if reach an invalid
    /// entry or a huge page (block descriptor) (spec mode).
    pub open spec fn spec_get_entry(self, vaddr: VAddr) -> (PTE, nat) {
        let pt_mem = self.pt_mem@;
        let p0e = PTE::spec_from_u64(pt_mem.read(pt_mem.root(), self.arch().pte_index(vaddr, 0)));
        if p0e.spec_valid() && !p0e.spec_huge() {
            let p1e = PTE::spec_from_u64(
                pt_mem.read(p0e.spec_addr(), self.arch().pte_index(vaddr, 1)),
            );
            if p1e.spec_valid() && !p1e.spec_huge() {
                let p2e = PTE::spec_from_u64(
                    pt_mem.read(p1e.spec_addr(), self.arch().pte_index(vaddr, 2)),
                );
                if p2e.spec_valid() && !p2e.spec_huge() {
                    (
                        PTE::spec_from_u64(
                            pt_mem.read(p2e.spec_addr(), self.arch().pte_index(vaddr, 3)),
                        ),
                        3,
                    )
                } else {
                    (p2e, 2)
                }
            } else {
                (p1e, 1)
            }
        } else {
            (p0e, 0)
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

    /// Get a page table entry and its level with virtual address, terminate if reach an invalid
    /// entry or a huge page (block descriptor).
    ///
    /// The behavior is proved to be consistent with `spec_get_entry`.
    pub fn get_entry(&self, vaddr: VAddrExec) -> (res: (PTE, usize))
        requires
            self.invariants(),
        ensures
            self.spec_get_entry(vaddr@) == (res.0, res.1 as nat),
    {
        proof {
            // Ensures root table is accessible
            let root = self.pt_mem@.root();
            self.pt_mem@.lemma_contains_root();
            self.pt_mem@.lemma_table_base_unique();
            self.pt_mem@.lemma_accessible(root, vaddr@, 0);
            assert(self.pt_mem@.accessible(root, self.arch().pte_index(vaddr@, 0)));
        }
        let p0e = PTE::from_u64(self.pt_mem.read(self.pt_mem.root(), pte_index(vaddr, 0)));
        if !p0e.valid() || p0e.huge() {
            return (p0e, 0);
        }
        // Invariants ensures the following access are valid

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

} // verus!
