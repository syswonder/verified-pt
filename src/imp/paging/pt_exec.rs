//! Executable page table implementation.
use std::marker::PhantomData;
use vstd::prelude::*;

use super::{pt::PageTable, pte::GenericPTE};
use crate::{
    common::{
        addr::{PAddrExec, VAddr, VAddrExec},
        arch::PTArch,
        frame::{Frame, FrameExec, MemAttr},
        PagingResult,
    },
    imp::tree::path::PTTreePath,
    spec::{interface::PTConstantsExec, memory::PageTableMemExec},
};

verus! {

// Use page table memory related lemmas.
broadcast use crate::spec::memory::group_pt_mem_lemmas;

/// Executable page table implementation.
///
/// `PageTable` wraps a `PageTableMemExec` and a `PTConstantsExec` to provide a convenient interface for
/// manipulating the page table. Refinement proof is provided by implementing trait `PageTableInterface`
/// to ensure `PageTableMemExec` is manipulated correctly.
pub struct PageTableExec<PTE: GenericPTE> {
    /// Page table memory.
    pub pt_mem: PageTableMemExec,
    /// Page table config constants.
    pub constants: PTConstantsExec,
    /// Phantom data.
    pub _phantom: PhantomData<PTE>,
}

impl<PTE> PageTableExec<PTE> where PTE: GenericPTE {
    /// View as a specification-level page table.
    pub open spec fn view(self) -> PageTable<PTE> {
        PageTable { pt_mem: self.pt_mem@, constants: self.constants@, _phantom: PhantomData }
    }

    /// Page table architecture specification.
    pub open spec fn spec_arch(self) -> PTArch {
        self.constants.arch@
    }

    /// Construct a new page table.
    pub fn new(pt_mem: PageTableMemExec, constants: PTConstantsExec) -> (res: Self)
        requires
            pt_mem@.arch == constants.arch@,
        ensures
            res@.invariants(),
            res.pt_mem == pt_mem,
            res.constants == constants,
    {
        let pt = Self { pt_mem, constants, _phantom: PhantomData };
        proof {
            // This is not true
            assume(pt@.invariants());
        }
        pt
    }

    pub open spec fn spec_new(pt_mem: PageTableMemExec, constants: PTConstantsExec) -> Self {
        Self { pt_mem, constants, _phantom: PhantomData }
    }

    /// Traverse the page table for the given virtual address and return the matching
    /// entry and level. Proven consistent with the specification-level walk.
    pub fn walk(&self, vaddr: VAddrExec, base: PAddrExec, level: usize) -> (res: (PTE, usize))
        requires
            self@.invariants(),
            self.pt_mem@.contains_table(base@),
            self.pt_mem@.table(base@).level == level,
        ensures
            (res.0, res.1 as nat) == self@.walk(vaddr@, base@, level as nat),
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        assert(self.pt_mem@.accessible(base@, idx as nat));
        let pte = PTE::from_u64(self.pt_mem.read(base, idx));
        if level < self.constants.arch.level_count() - 1 && pte.valid() && !pte.huge() {
            self.walk(vaddr, pte.addr(), level + 1)
        } else {
            (pte, level)
        }
    }

    /// Insert a page table entry into the page table, creates intermediate tables if necessary.
    ///
    /// `target_level` is the level at which the entry should be inserted.
    /// `new_pte` is the entry to be inserted.
    pub fn insert(
        &mut self,
        vbase: VAddrExec,
        base: PAddrExec,
        level: usize,
        target_level: usize,
        new_pte: PTE,
    ) -> (res: PagingResult)
        requires
            old(self)@.invariants(),
            level <= target_level < old(self).spec_arch().level_count(),
            old(self).pt_mem@.contains_table(base@),
            old(self).pt_mem@.table(base@).level == level,
            old(self)@.pte_points_to_frame(new_pte, target_level as nat),
        ensures
            (self@, res) == old(self)@.insert(
                vbase@,
                base@,
                level as nat,
                target_level as nat,
                new_pte,
            ),
            res is Err ==> old(self) == self,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        assert(self.pt_mem@.accessible(base@, idx as nat));
        let pte = PTE::from_u64(self.pt_mem.read(base, idx));
        if level >= target_level {
            // Insert at current level
            if pte.valid() {
                PagingResult::Err(())
            } else {
                self.pt_mem.write(base, idx, new_pte.to_u64());
                PagingResult::Ok(())
            }
        } else {
            if pte.valid() {
                if pte.huge() {
                    PagingResult::Err(())
                } else {
                    // Insert at next level
                    self.insert(vbase, pte.addr(), level + 1, target_level, new_pte)
                }
            } else {
                // Insert intermediate table
                proof {
                    // Lemma ensures this branch returns Ok
                    self@.lemma_insert_intermediate_node_results_ok(
                        vbase@,
                        base@,
                        level as nat,
                        target_level as nat,
                        new_pte,
                    );
                }
                // Allocate a new table
                let table = self.pt_mem.alloc_table(level + 1);
                // Write entry
                let pte = PTE::new(table.base, MemAttr::default(), false);
                self.pt_mem.write(base, idx, pte.to_u64());
                proof {
                    assert(self.pt_mem@.contains_table(table.base@));
                    // TODO
                    assume(self@.invariants());
                }
                let res = self.insert(vbase, table.base, level + 1, target_level, new_pte);
                res
            }
        }
    }

    /// Recursively remove a page table entry.
    pub fn remove(&mut self, vbase: VAddrExec, base: PAddrExec, level: usize) -> (res: PagingResult)
        requires
            old(self)@.invariants(),
            level < old(self).spec_arch().level_count(),
            old(self).pt_mem@.contains_table(base@),
            old(self).pt_mem@.table(base@).level == level,
        ensures
            (self@, res) == old(self)@.remove(vbase@, base@, level as nat),
            res is Err ==> old(self) == self,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        assert(self.pt_mem@.accessible(base@, idx as nat));
        let pte = PTE::from_u64(self.pt_mem.read(base, idx));
        if pte.valid() {
            if level >= self.constants.arch.level_count() - 1 {
                // Leaf node
                if vbase.aligned(self.constants.arch.frame_size(level).as_usize()) {
                    self.pt_mem.write(base, idx, PTE::empty().to_u64());
                    PagingResult::Ok(())
                } else {
                    PagingResult::Err(())
                }
            } else {
                // Intermediate node
                if pte.huge() {
                    if vbase.aligned(self.constants.arch.frame_size(level).as_usize()) {
                        self.pt_mem.write(base, idx, PTE::empty().to_u64());
                        PagingResult::Ok(())
                    } else {
                        PagingResult::Err(())
                    }
                } else {
                    self.remove(vbase, pte.addr(), level + 1)
                }
            }
        } else {
            PagingResult::Err(())
        }
    }

    /// Recursively remove empty nodes along `vaddr` from `base`.
    pub fn recycle(&mut self, vaddr: VAddrExec, base: PAddrExec, level: usize)
        requires
            old(self)@.invariants(),
            level < old(self).spec_arch().level_count(),
            old(self).pt_mem@.contains_table(base@),
            old(self).pt_mem@.table(base@).level == level,
        ensures
            self@ == old(self)@.recycle(vaddr@, base@, level as nat),
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        assert(self.pt_mem@.accessible(base@, idx as nat));
        let pte = PTE::from_u64(self.pt_mem.read(base, idx));
        if level < self.constants.arch.level_count() - 1 && pte.valid() && !pte.huge() {
            // Recycle subnode
            proof {
                self.view().lemma_recycle_preserves_invariants(
                    vaddr@,
                    pte.spec_addr(),
                    level as nat + 1,
                );
                self.view().lemma_recycle_preserves_current(
                    vaddr@,
                    pte.spec_addr(),
                    level as nat + 1,
                );
            }
            self.recycle(vaddr, pte.addr(), level + 1);
            assume(self.pt_mem@.accessible(base@, idx as nat));

            if self.pt_mem.is_table_empty(pte.addr()) {
                // If subnode is empty, deallocate the table, and mark the entry as invalid
                assume(self.pt_mem@.root() != pte.spec_addr());
                proof {
                    self.pt_mem.view().lemma_dealloc_table_preserves_accessibility(
                        pte.spec_addr(),
                        base@,
                        idx as nat,
                    );
                }
                self.pt_mem.dealloc_table(pte.addr());
                assert(self.pt_mem@.contains_table(base@));
                self.pt_mem.write(base, idx, PTE::empty().to_u64());
            }
        }
    }

    /// Resolve a virtual address to its mapped physical frame.
    pub fn query(&self, vaddr: VAddrExec) -> (res: PagingResult<(VAddrExec, FrameExec)>)
        requires
            self@.invariants(),
        ensures
            self@@.query(vaddr@) == match res {
                PagingResult::Ok((vaddr, frame)) => PagingResult::Ok((vaddr@, frame@)),
                PagingResult::Err(_) => PagingResult::Err(()),
            },
    {
        let (pte, level) = self.walk(vaddr, self.pt_mem.root(), 0);
        proof {
            // spec `get_pte` == node `visit`
            self.pt_mem@.lemma_contains_root();
            self@.lemma_construct_node_implies_invariants(self.pt_mem@.root(), 0);
            let node = self@.construct_node(self.pt_mem@.root(), 0);
            self@.lemma_walk_consistent_with_model(vaddr@, self.pt_mem@.root(), 0);
            node.lemma_visit_length_bounds(
                PTTreePath::from_vaddr_root(
                    vaddr@,
                    self.spec_arch(),
                    (self.spec_arch().level_count() - 1) as nat,
                ),
            );
            assert(level < self.spec_arch().level_count());
            // exec `query` consistent with model `query`
            if pte.spec_valid() {
                assert(self@@.query(vaddr@) == PagingResult::Ok(
                    (
                        self.spec_arch().vbase(vaddr@, level as nat),
                        Frame {
                            base: pte.spec_addr(),
                            size: self.spec_arch().frame_size(level as nat),
                            attr: pte.spec_attr(),
                        },
                    ),
                ));
            } else {
                assert(self@@.query(vaddr@) == PagingResult::<(VAddr, Frame)>::Err(()));
            }
        }
        if pte.valid() {
            Ok(
                (
                    self.constants.arch.vbase(vaddr, level),
                    FrameExec {
                        base: pte.addr(),
                        size: self.constants.arch.frame_size(level),
                        attr: pte.attr(),
                    },
                ),
            )
        } else {
            Err(())
        }
    }

    /// Insert a mapping from a virtual base address to a physical frame.
    pub fn map(&mut self, vbase: VAddrExec, frame: FrameExec) -> (res: PagingResult)
        requires
            old(self)@.invariants(),
            old(self)@.constants.arch.is_valid_frame_size(frame.size),
            vbase@.aligned(frame.size.as_nat()),
            frame.base@.aligned(frame.size.as_nat()),
            frame.base.0 >= old(self).constants.pmem_lb.0,
            frame.base.0 + frame.size.as_nat() <= old(self).constants.pmem_ub.0,
        ensures
            self@.invariants(),
            ({
                let (s2, r) = old(self)@@.map(vbase@, frame@);
                r is Ok == res is Ok && s2 == self@@
            }),
    {
        let target_level = self.constants.arch.level_of_frame_size(frame.size);
        let huge = target_level < self.constants.arch.level_count() - 1;
        let new_pte = PTE::new(frame.base, frame.attr, huge);

        proof {
            let root = self.pt_mem@.root();
            // Ensures #1
            self.view().lemma_insert_preserves_invariants(
                vbase@,
                root,
                0,
                target_level as nat,
                new_pte,
            );
            // Ensures #2
            self.view().lemma_insert_consistent_with_model(
                vbase@,
                root,
                0,
                target_level as nat,
                new_pte,
            );
            self.view().lemma_insert_preserves_root(vbase@, root, 0, target_level as nat, new_pte);
        }

        self.insert(vbase, self.pt_mem.root(), 0, target_level, new_pte)
    }

    /// Remove the mapping for a given virtual base address.
    pub fn unmap(&mut self, vbase: VAddrExec) -> (res: PagingResult)
        requires
            old(self)@.invariants(),
        ensures
            self@.invariants(),
            ({
                let (s2, r) = old(self)@@.unmap(vbase@);
                r is Ok == res is Ok && s2 == self@@
            }),
    {
        proof {
            let root = self.pt_mem@.root();
            // Ensures #1
            self@.lemma_remove_preserves_invariants(vbase@, root, 0);
            // Ensures #2
            self@.lemma_remove_consistent_with_model(vbase@, root, 0);
            self@.lemma_remove_preserves_root(vbase@, root, 0);
        }

        self.remove(vbase, self.pt_mem.root(), 0)
    }
}

} // verus!
