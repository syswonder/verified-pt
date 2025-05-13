//! Executable page table implementation.
use std::marker::PhantomData;
use vstd::prelude::*;

use super::{
    arch::{VMSAv8_4kHelpers, VMSAV8_4K_ARCH},
    pte::GenericPTE,
};
use crate::{
    common::{
        addr::{PAddr, PAddrExec, VAddr, VAddrExec},
        arch::{PTArch, PTArchHelpers},
        frame::{Frame, FrameExec},
        PagingResult,
    },
    imp::tree::{
        model::PTTreeModel,
        node::{NodeEntry, PTTreeNode},
        path::PTTreePath,
    },
    spec::{interface::PTConstantsExec, page_table::PageTableState, memory::PageTableMemExec},
};

verus! {

/// Executable 4-level page table implementation.
///
/// Only support VMSAv8-64 page table using 4K granule yet, but can be extended to other
/// architectures in future works.
pub struct PageTable<PTE: GenericPTE> {
    /// Page table memory, arch is `VMSAV8_4K_ARCH`
    pub pt_mem: PageTableMemExec,
    /// Page table config constants.
    pub constants: PTConstantsExec,
    /// Phantom data.
    pub _phantom: PhantomData<PTE>,
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
        &&& self.constants.arch@ == VMSAV8_4K_ARCH
        // Page table memory invariants
        &&& self.pt_mem@.invariants()
        // Each table descriptor that can be accessed must satisfy
        &&& forall|base: PAddr, idx: nat|
            self.pt_mem@.accessible(base, idx) ==> {
                let pt_mem = self.pt_mem@;
                let table = pt_mem.table(base);
                let pte = PTE::spec_from_u64(pt_mem.read(base, idx));
                // If `table` is not a leaf table, `pte` is valid and points to a table...
                // then `pt_mem` contains the table, and the table level is one level higher than `base`
                &&& ({
                    &&& table.level != self.arch().level_count()
                    &&& pte.spec_valid()
                    &&& !pte.spec_huge()
                }) ==> {
                    &&& pt_mem.contains_table(pte.spec_addr())
                    &&& pt_mem.table(pte.spec_addr()).level == pt_mem.table(base).level + 1
                }
                // If `table` is a leaf table, `pte` is either invalid or points to a frame
                &&& (table.level == self.arch().level_count() && pte.spec_valid())
                    ==> !pte.spec_huge()
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
            constants: self.constants@,
            level,
            entries,
        }
    }

    /// Lemma. The node returned by `build_node` satisfies the invariants.
    pub proof fn lemma_build_node_implies_invariants(self, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem@.contains_table(base),
            level == self.pt_mem@.table(base).level,
            level < self.arch().level_count(),
        ensures
            self.build_node(base, level).invariants(),
    {
        // TODO
        assume(false)
    }

    /// Lemma. The tree model returned by `view` satisfies the invariants.
    pub proof fn lemma_view_implies_invariants(self)
        requires
            self.invariants(),
        ensures
            self.view().invariants(),
    {
        self.pt_mem@.lemma_contains_root();
        self.lemma_build_node_implies_invariants(self.pt_mem@.root(), 0);
    }

    /// Get a page table entry and its level with virtual address, terminate if reach an invalid
    /// entry or a huge page (block descriptor) (spec mode).
    pub open spec fn spec_get_pte(self, vaddr: VAddr) -> (PTE, nat) {
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

    /// Recursively get a page table entry and its level with virtual address, terminate if reach an invalid
    /// entry or a huge page (block descriptor) (spec mode).
    pub open spec fn spec_recursive_get_pte(self, vaddr: VAddr, base: PAddr, level: nat) -> (
        PTE,
        nat,
    )
        recommends
            self.invariants(),
            level < self.arch().level_count(),
        decreases self.arch().level_count() - level,
    {
        let pte = PTE::spec_from_u64(self.pt_mem@.read(base, self.arch().pte_index(vaddr, level)));
        if level >= self.arch().level_count() - 1 {
            (pte, level)
        } else {
            if pte.spec_valid() && !pte.spec_huge() {
                self.spec_recursive_get_pte(vaddr, pte.spec_addr(), level + 1)
            } else {
                (pte, level)
            }
        }
    }

    /// Construct a new page table.
    pub fn new(pt_mem: PageTableMemExec, constants: PTConstantsExec) -> (res: Self)
        requires
            pt_mem@.arch == VMSAV8_4K_ARCH,
        ensures
            res.invariants(),
            res.pt_mem == pt_mem,
            res.constants == constants,
    {
        let pt = Self { pt_mem, constants, _phantom: PhantomData };
        proof {
            assume(pt.invariants());
        }
        pt
    }

    /// Get a page table entry and its level with virtual address, terminate if reach an invalid
    /// entry or a huge page (block descriptor).
    ///
    /// The behavior is proved to be consistent with `spec_get_pte`.
    pub fn get_pte(&self, vaddr: VAddrExec) -> (res: (PTE, usize))
        requires
            self.invariants(),
        ensures
            self.spec_get_pte(vaddr@) == (res.0, res.1 as nat),
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
        let (pte, level) = self.get_pte(vaddr);
        proof {
            // exec `get_pte` == spec `get_pte` == spec `recursive_get_pte`
            self.lemma_recursive_get_pte_consistent_with_get_pte(vaddr@);
            // spec `recursive_get_pte` == node `recursive_visit`
            self.lemma_recursive_get_pte_consistent_with_recursive_visit(vaddr@);
            // exec `query` consistent with model `query`
            if pte.spec_valid() {
                assert(self@.query(vaddr@) == PagingResult::Ok(
                    (
                        self.arch().vbase(vaddr@, level as nat),
                        Frame {
                            base: pte.spec_addr(),
                            size: self.arch().frame_size(level as nat),
                            attr: pte.spec_attr(),
                        },
                    ),
                ));
            } else {
                assert(self@.query(vaddr@) == PagingResult::<(VAddr, Frame)>::Err(()));
            }
        }
        if pte.valid() {
            Ok(
                (
                    VMSAv8_4kHelpers::vbase(vaddr, level),
                    FrameExec {
                        base: pte.addr(),
                        size: VMSAv8_4kHelpers::frame_size(level),
                        attr: pte.attr(),
                    },
                ),
            )
        } else {
            Err(())
        }
    }

    /// Map a virtual address to a physical frame.
    pub fn map(&mut self, vbase: VAddrExec, frame: FrameExec) -> (res: PagingResult)
        requires
            old(self).invariants(),
            old(self).arch().is_valid_frame_size(frame.size),
            vbase@.aligned(frame.size.as_nat()),
            frame.base@.aligned(frame.size.as_nat()),
            frame.base.0 >= old(self).constants.pmem_lb.0,
            frame.base.0 + frame.size.as_nat() <= old(self).constants.pmem_ub.0,
        ensures
            self.invariants(),
            old(self)@.map(vbase@, frame@) == match res {
                Ok(()) => Ok(self@),
                Err(()) => Err(()),
            },
            res is Err ==> old(self) == self,
    {
        // TODO
        assume(false);
        Err(())
    }

    /// Unmap a virtual address.
    pub fn unmap(&mut self, vbase: VAddrExec) -> (res: PagingResult)
        requires
            old(self).invariants(),
        ensures
            self.invariants(),
            old(self)@.unmap(vbase@) == match res {
                Ok(()) => Ok(self@),
                Err(()) => Err(()),
            },
            res is Err ==> old(self) == self,
    {
        // TODO
        assume(false);
        Err(())
    }

    /// Lemma. `sepc_recursive_get_pte` is consistent with `spec_get_pte`.
    pub proof fn lemma_recursive_get_pte_consistent_with_get_pte(self, vaddr: VAddr)
        requires
            self.invariants(),
        ensures
            self.spec_recursive_get_pte(vaddr, self.pt_mem@.root(), 0) == self.spec_get_pte(vaddr),
    {
        // TODO
        assume(false);
    }

    /// Lemma. `spec_recursive_get_pte` is consistent with `PTTreeNode::recursive_visit`.
    pub proof fn lemma_recursive_get_pte_consistent_with_recursive_visit(self, vaddr: VAddr)
        requires
            self.invariants(),
        ensures
            ({
                let (pte, level) = self.spec_recursive_get_pte(vaddr, self.pt_mem@.root(), 0);
                let node = self.build_node(self.pt_mem@.root(), 0);
                let visited = node.recursive_visit(
                    PTTreePath::from_vaddr(
                        vaddr,
                        self.arch(),
                        (self.arch().level_count() - 1) as nat,
                    ),
                );
                visited.len() == level + 1 && visited.last() == if pte.spec_valid() {
                    NodeEntry::Frame(
                        Frame {
                            base: pte.spec_addr(),
                            size: self.arch().frame_size(level),
                            attr: pte.spec_attr(),
                        },
                    )
                } else {
                    NodeEntry::Empty
                }
            }),
    {
        let (pte, level) = self.spec_recursive_get_pte(vaddr, self.pt_mem@.root(), 0);
        let node = self.build_node(self.pt_mem@.root(), 0);
        let entry = node.recursive_visit(
            PTTreePath::from_vaddr(vaddr, self.arch(), (self.arch().level_count() - 1) as nat),
        ).last();

        self.pt_mem@.lemma_contains_root();
        self.lemma_build_node_implies_invariants(self.pt_mem@.root(), 0);
        assert(node.invariants());
        // TODO
        assume(false);
    }

    /// Theorem. Page table walk behavior defined by `PageTable::view()` and `PageTableMem::interpret()`
    /// must be consistent.
    ///
    /// This theroem is needed because we must ensure the hardware and the OS interpret the page table
    /// in the same way.
    pub proof fn lemma_view_consistent_with_interpret(self)
        requires
            self.invariants(),
        ensures
            self.view().view() == PageTableState::new(self.pt_mem@.interpret(), self.constants@)
    {
        // TODO
        assume(false);
    }
}

} // verus!
