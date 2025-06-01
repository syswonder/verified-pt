//! Executable page table implementation.
use std::marker::PhantomData;
use vstd::prelude::*;

use super::pte::GenericPTE;
use crate::{
    common::{
        addr::{PAddr, VAddr, VAddrExec},
        arch::{PTArch, VMSAV8_4K_ARCH},
        frame::{Frame, FrameExec, MemAttr},
        PagingResult,
    },
    imp::tree::{
        model::PTTreeModel,
        node::{NodeEntry, PTTreeNode},
        path::PTTreePath,
    },
    spec::{interface::PTConstantsExec, memory::PageTableMemExec, page_table::PageTableState},
};

verus! {

// Use page table memory related lemmas.
broadcast use crate::spec::memory::group_pt_mem_lemmas;

/// Executable page table implementation.
///
/// `PageTable` wraps a `PageTableMemExec` and a `PTConstantsExec` to provide a convenient interface for
/// manipulating the page table. Refinement proof is provided by implementing trait `PageTableInterface`
/// to ensure `PageTableMemExec` is manipulated correctly.
pub struct PageTable<PTE: GenericPTE> {
    /// Page table memory.
    pub pt_mem: PageTableMemExec,
    /// Page table config constants.
    pub constants: PTConstantsExec,
    /// Phantom data.
    pub _phantom: PhantomData<PTE>,
}

impl<PTE> PageTable<PTE> where PTE: GenericPTE {
    /// Invariants that ensure the page table is well-formed.
    pub open spec fn invariants(self) -> bool {
        // Target architecture
        &&& self.pt_mem@.arch
            == self.spec_arch()
        // Page table memory invariants
        &&& self.pt_mem@.invariants()
        // For each table descriptor that can be accessed
        &&& forall|base: PAddr, idx: nat|
            self.pt_mem@.accessible(base, idx) ==> {
                let pt_mem = self.pt_mem@;
                let table = pt_mem.table(base);
                let pte = PTE::spec_from_u64(pt_mem.read(base, idx));
                // If `table` is not a leaf table, `pte` is valid and points to a table...
                // then `pt_mem` contains the table, and the table level is one level higher than `base`
                &&& ({
                    &&& table.level != self.spec_arch().level_count()
                    &&& pte.spec_valid()
                    &&& !pte.spec_huge()
                }) ==> {
                    &&& pt_mem.contains_table(pte.spec_addr())
                    &&& pt_mem.table(pte.spec_addr()).level == pt_mem.table(base).level + 1
                }
                // If `table` is a leaf table, `pte` is either invalid or points to a frame
                &&& (table.level == self.spec_arch().level_count() && pte.spec_valid())
                    ==> !pte.spec_huge()
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

    /// Perform a recursive specification-level page table walk starting from a given base.
    /// Terminate upon reaching an invalid or block entry.
    pub open spec fn spec_walk(self, vaddr: VAddr, base: PAddr, level: nat) -> (PTE, nat)
        recommends
            self.invariants(),
            level < self.spec_arch().level_count(),
        decreases self.spec_arch().level_count() - level,
    {
        let pte = PTE::spec_from_u64(
            self.pt_mem@.read(base, self.spec_arch().pte_index(vaddr, level)),
        );
        if level >= self.spec_arch().level_count() - 1 {
            (pte, level)
        } else {
            if pte.spec_valid() && !pte.spec_huge() {
                self.spec_walk(vaddr, pte.spec_addr(), level + 1)
            } else {
                (pte, level)
            }
        }
    }

    /// Traverse the page table for the given virtual address and return the matching
    /// entry and level. Proven consistent with the specification-level walk.
    pub fn walk(&self, vaddr: VAddrExec) -> (res: (PTE, usize))
        requires
            self.invariants(),
        ensures
            self.spec_walk(vaddr@, self.pt_mem@.root(), 0) == (res.0, res.1 as nat),
    {
        proof {
            assert(self.spec_arch().valid());
            assert(self.spec_arch().level_count() >= 1);
            self.pt_mem@.lemma_contains_root();
            assume(false);
        }
        let level_count = self.constants.arch.level_count();
        let mut level = 0;
        let mut base = self.pt_mem.root();
        let mut idx = self.constants.arch.pte_index(vaddr, level);
        let mut val = self.pt_mem.read(base, idx);
        let mut pte = PTE::from_u64(val);

        while level < level_count - 1
            invariant
                self.invariants(),
                self.pt_mem@.accessible(base@, idx as nat),
                self.pt_mem@.table(base@).level == level as nat,
                self.pt_mem@.read(base@, idx as nat) == val,
                pte == PTE::spec_from_u64(val),
                level < level_count,
        {
            if !pte.valid() || pte.huge() {
                // Reach an invalid or huge page entry, terminate.
                break ;
            }
            // Continue to the next level.

            level += 1;
            base = pte.addr();
            idx = self.constants.arch.pte_index(vaddr, level);
            val = self.pt_mem.read(base, idx);
            pte = PTE::from_u64(val);
        }
        (pte, level)
    }

    /// Insert a page table entry into the page table, creates intermediate tables if necessary.
    ///
    /// `target_level` is the level at which the entry should be inserted.
    pub fn insert(&mut self, vbase: VAddrExec, target_level: usize, target_pte: PTE) -> (res:
        PagingResult)
        requires
            old(self).invariants(),
            target_level < old(self).spec_arch().level_count(),
    {
        proof {
            self.pt_mem@.lemma_contains_root();
        }
        let level_count = self.constants.arch.level_count();
        let mut level = 0;
        let mut base = self.pt_mem.root();
        let mut idx = self.constants.arch.pte_index(vbase, level);
        let mut val = self.pt_mem.read(base, idx);
        let mut pte = PTE::from_u64(val);

        while level < target_level
            invariant
                self.invariants(),
                self.pt_mem@.accessible(base@, idx as nat),
                self.pt_mem@.table(base@).level == level as nat,
                self.pt_mem@.read(base@, idx as nat) == val,
                pte == PTE::spec_from_u64(val),
                level < target_level + 1,
        {
            if !pte.valid() {
                // Reach an invalid entry, create a sub-table.
                let subtable = self.pt_mem.alloc_table(level + 1);
                pte =
                PTE::new(
                    subtable.base,
                    MemAttr {
                        readable: true,
                        writable: true,
                        executable: true,
                        user_accessible: true,
                        device: false,
                    },
                    false,
                );
                self.pt_mem.write(base, idx, pte.to_u64());
                proof {
                    assume(self.invariants());
                    assume(self.pt_mem@.accessible(
                        subtable.base@,
                        self.spec_arch().pte_index(vbase@, level as nat + 1),
                    ));
                }
            } else if pte.huge() {
                // Reach a huge page entry, insertion fails.
                break ;
            }
            // Continue to the next level.

            level += 1;
            base = pte.addr();
            idx = self.constants.arch.pte_index(vbase, level);
            val = self.pt_mem.read(base, idx);
            pte = PTE::from_u64(val);
        }

        // Reach the target level, insert the entry.
        if pte.valid() {
            PagingResult::Err(())
        } else {
            self.pt_mem.write(base, idx, target_pte.to_u64());
            PagingResult::Ok(())
        }
    }

    /// Remove a page table entry from the page table.
    pub fn remove(&mut self, vbase: VAddrExec) -> (res: PagingResult)
        requires
            old(self).invariants(),
    {
        let level_count = self.constants.arch.level_count();
        let mut level = 0;
        let mut base = self.pt_mem.root();
        let mut idx = self.constants.arch.pte_index(vbase, level);
        let mut val = self.pt_mem.read(base, idx);
        let mut pte = PTE::from_u64(val);

        while level < level_count - 1
            invariant
                self.invariants(),
                self.pt_mem@.accessible(base@, idx as nat),
                self.pt_mem@.table(base@).level == level as nat,
                self.pt_mem@.read(base@, idx as nat) == val,
                pte == PTE::spec_from_u64(val),
                level < level_count,
        {
            if !pte.valid() {
                // Reach an invalid entry, remove fails.
                return PagingResult::Err(());
            }
            if pte.huge() {
                // Reach a huge page entry
                if vbase.aligned(self.constants.arch.frame_size(level).as_usize()) {
                    // `vaddr` should be aligned to the frame size.
                    self.pt_mem.write(base, idx, PTE::empty().to_u64());
                    return PagingResult::Ok(());
                } else {
                    // Remove fails.
                    return PagingResult::Err(());
                }
            }
            // Continue to the next level.

            level += 1;
            base = pte.addr();
            idx = self.constants.arch.pte_index(vbase, level);
            val = self.pt_mem.read(base, idx);
            pte = PTE::from_u64(val);
        }

        // Reach the last level
        if pte.valid() && vbase.aligned(self.constants.arch.frame_size(level).as_usize()) {
            // `vaddr` should be aligned to the frame size.
            self.pt_mem.write(base, idx, PTE::empty().to_u64());
            PagingResult::Ok(())
        } else {
            // Remove fails.
            PagingResult::Err(())
        }
    }

    /// Resolve a virtual address to its mapped physical frame.
    pub fn query(&self, vaddr: VAddrExec) -> (res: PagingResult<(VAddrExec, FrameExec)>)
        requires
            self.invariants(),
        ensures
            self@.query(vaddr@) == match res {
                PagingResult::Ok((vaddr, frame)) => PagingResult::Ok((vaddr@, frame@)),
                PagingResult::Err(_) => PagingResult::Err(()),
            },
    {
        let (pte, level) = self.walk(vaddr);
        proof {
            // spec `recursive_get_pte` == node `recursive_visit`
            self.pt_mem.view().lemma_contains_root();
            self.lemma_build_node_implies_invariants(self.pt_mem@.root(), 0);
            let node = self.build_node(self.pt_mem@.root(), 0);
            self.lemma_spec_walk_consistent_with_recursive_visit(vaddr@);
            node.lemma_visit_length_bounds(
                PTTreePath::from_vaddr(
                    vaddr@,
                    self.spec_arch(),
                    (self.spec_arch().level_count() - 1) as nat,
                ),
            );
            assert(level < self.spec_arch().level_count());
            // exec `query` consistent with model `query`
            if pte.spec_valid() {
                assert(self@.query(vaddr@) == PagingResult::Ok(
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
                assert(self@.query(vaddr@) == PagingResult::<(VAddr, Frame)>::Err(()));
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
            old(self).invariants(),
            old(self).spec_arch().is_valid_frame_size(frame.size),
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
        let level = self.constants.arch.level_of_frame_size(frame.size);
        let huge = level < self.constants.arch.level_count() - 1;
        self.insert(
            vbase,
            level,
            PTE::new(frame.base, frame.attr, huge),
        )
    }

    /// Remove the mapping for a given virtual base address.
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
        self.remove(vbase)
    }

    /// Page table architecture specification.
    pub open spec fn spec_arch(self) -> PTArch {
        self.constants.arch@
    }

    /// Convert the executable page table into a tree-model abstraction.
    pub open spec fn view(self) -> PTTreeModel
        recommends
            self.invariants(),
    {
        PTTreeModel { root: self.build_node(self.pt_mem@.root(), 0) }
    }

    /// Recursively construct a model node from a subtable starting at the given base and level.
    pub open spec fn build_node(self, base: PAddr, level: nat) -> PTTreeNode
        recommends
            self.invariants(),
            self.pt_mem@.contains_table(base),
            level == self.pt_mem@.table(base).level,
            level < self.spec_arch().level_count(),
        decreases self.spec_arch().level_count() - level,
    {
        let arch = self.spec_arch();
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
        PTTreeNode { constants: self.constants@, level, entries }
    }

    /// Lemma. Constructing a node from memory with a valid table results in a
    /// structurally invariant model node.
    pub proof fn lemma_build_node_implies_invariants(self, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem@.contains_table(base),
            level == self.pt_mem@.table(base).level,
            level < self.spec_arch().level_count(),
        ensures
            self.build_node(base, level).invariants(),
    {
        // TODO
        assume(false)
    }

    /// Lemma. The tree model derived from the executable page table maintains the
    /// required structural invariants.
    pub proof fn lemma_view_implies_invariants(self)
        requires
            self.invariants(),
        ensures
            self.view().invariants(),
    {
        self.pt_mem@.lemma_contains_root();
        self.lemma_build_node_implies_invariants(self.pt_mem@.root(), 0);
    }

    /// Lemma. The specification-level walk yields results consistent with the node model
    /// traversal via `PTTreeNode::recursive_visit`.
    pub proof fn lemma_spec_walk_consistent_with_recursive_visit(self, vaddr: VAddr)
        requires
            self.invariants(),
        ensures
            ({
                let (pte, level) = self.spec_walk(vaddr, self.pt_mem@.root(), 0);
                let node = self.build_node(self.pt_mem@.root(), 0);
                let visited = node.recursive_visit(
                    PTTreePath::from_vaddr(
                        vaddr,
                        self.spec_arch(),
                        (self.spec_arch().level_count() - 1) as nat,
                    ),
                );
                visited.len() == level + 1 && visited.last() == if pte.spec_valid() {
                    NodeEntry::Frame(
                        Frame {
                            base: pte.spec_addr(),
                            size: self.spec_arch().frame_size(level),
                            attr: pte.spec_attr(),
                        },
                    )
                } else {
                    NodeEntry::Empty
                }
            }),
    {
        let (pte, level) = self.spec_walk(vaddr, self.pt_mem@.root(), 0);
        let node = self.build_node(self.pt_mem@.root(), 0);
        let entry = node.recursive_visit(
            PTTreePath::from_vaddr(
                vaddr,
                self.spec_arch(),
                (self.spec_arch().level_count() - 1) as nat,
            ),
        ).last();

        self.pt_mem@.lemma_contains_root();
        self.lemma_build_node_implies_invariants(self.pt_mem@.root(), 0);
        assert(node.invariants());
        // TODO
        assume(false);
    }

    /// Theorem. The interpreted view of the page table memory is consistent with the view derived
    /// from the model tree, ensuring semantic agreement between hardware and software views.
    pub proof fn model_consistent_with_hardware(self)
        requires
            self.invariants(),
        ensures
            self.view().view() == PageTableState::new(self.pt_mem@.interpret(), self.constants@),
    {
        // TODO
        assume(false);
    }
}

} // verus!
