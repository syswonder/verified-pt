//! Executable page table implementation.
use std::marker::PhantomData;
use vstd::prelude::*;

use super::{
    arch::{VMSAv8_4kHelpers, VMSAV8_4K_ARCH},
    pt_mem::PageTableMemExec,
    pte::GenericPTE,
};
use crate::{
    common::{
        addr::{PAddr, PAddrExec, VAddr, VAddrExec},
        arch::{PTArch, PTArchHelpers},
        frame::{Frame, FrameExec, FrameSize},
        PagingResult,
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
        let p0e = PTE::from_u64(
            self.pt_mem.read(self.pt_mem.root(), VMSAv8_4kHelpers::pte_index(vaddr, 0)),
        );
        if !p0e.valid() || p0e.huge() {
            return (p0e, 0);
        }
        // Invariants ensures the following access are valid
        let p1e = PTE::from_u64(
            self.pt_mem.read(p0e.addr(), VMSAv8_4kHelpers::pte_index(vaddr, 1)),
        );
        if !p1e.valid() || p1e.huge() {
            return (p1e, 1);
        }
        let p2e = PTE::from_u64(
            self.pt_mem.read(p1e.addr(), VMSAv8_4kHelpers::pte_index(vaddr, 2)),
        );
        if !p2e.valid() || p2e.huge() {
            return (p2e, 2);
        }
        let p3e = PTE::from_u64(
            self.pt_mem.read(p2e.addr(), VMSAv8_4kHelpers::pte_index(vaddr, 3)),
        );
        (p3e, 3)
    }

    /// Query a virtual address, return the mapped physical frame.
    pub fn query(&self, vaddr: VAddrExec) -> (res: PagingResult<(VAddrExec, FrameExec)>)
        requires
            self.invariants(),
        ensures
            self@.query(vaddr@) == match res {
                PagingResult::Ok((vaddr, frame)) => PagingResult::Ok((vaddr@, frame@)),
                PagingResult::Err(_) => PagingResult::Err(()),
            },
    {
        proof {
            // TODO
            assume(false);
        }
        let (entry, level) = self.get_entry(vaddr);
        if entry.valid() {
            Ok(
                (
                    VMSAv8_4kHelpers::vbase(vaddr, level),
                    FrameExec {
                        base: entry.addr(),
                        size: VMSAv8_4kHelpers::frame_size(level),
                        attr: entry.attr(),
                    },
                ),
            )
        } else {
            Err(())
        }
    }
}

} // verus!
