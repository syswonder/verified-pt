//! Executable page table implementation.
use std::marker::PhantomData;
use vstd::prelude::*;

use super::pte::GenericPTE;
use crate::{
    common::{
        addr::{PAddr, VAddr, VAddrExec},
        arch::PTArch,
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
            pt_mem@.arch == constants.arch@,
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

    /// Traverse the page table for the given virtual address and return the matching
    /// entry and level. Proven consistent with the specification-level walk.
    pub fn walk(&self, vaddr: VAddrExec) -> (res: (PTE, usize))
        requires
            self.invariants(),
        ensures
            ({
                let ptes = self.spec_walk(
                    vaddr@,
                    self.pt_mem@.root(),
                    0,
                    (self.spec_arch().level_count() - 1) as nat,
                );
                res.0 == ptes.last() && res.1 == ptes.len() - 1
            }),
    {
        proof {
            assert(self.spec_arch().valid());
            assert(self.spec_arch().level_count() >= 1);
            self.pt_mem@.lemma_contains_root();
        }
        let stop_level = self.constants.arch.level_count() - 1;
        let mut level = 0;
        let mut base = self.pt_mem.root();
        let mut idx = self.constants.arch.pte_index(vaddr, level);
        let mut val = self.pt_mem.read(base, idx);
        let mut pte = PTE::from_u64(val);

        while level < stop_level
            invariant
                self.invariants(),
                self.pt_mem@.accessible(base@, idx as nat),
                self.pt_mem@.table(base@).level == level as nat,
                self.pt_mem@.read(base@, idx as nat) == val,
                stop_level == self.spec_arch().level_count() - 1,
                pte == PTE::spec_from_u64(val),
                level <= stop_level,
                ({
                    let ptes = self.spec_walk(vaddr@, self.pt_mem@.root(), 0, level as nat);
                    pte == ptes.last() && level == ptes.len() - 1
                }),
        {
            if !pte.valid() || pte.huge() {
                proof {
                    if level > 0 {
                        let ptes1 = self.spec_walk(vaddr@, self.pt_mem@.root(), 0, level as nat);
                        self.lemma_full_walk_stabilizes(
                            vaddr@,
                            self.pt_mem@.root(),
                            0,
                            level as nat,
                            (self.spec_arch().level_count() - 1) as nat,
                        );
                    }
                }
                // Reach an invalid or huge page entry, terminate.
                return (pte, level);
            }
            // Continue to the next level.

            let ghost ptes1 = self.spec_walk(vaddr@, self.pt_mem@.root(), 0, level as nat);
            let ghost ptes2 = self.spec_walk(vaddr@, self.pt_mem@.root(), 0, level as nat + 1);
            proof {
                assert(pte == ptes1.last());
                self.lemma_extend_walk_by_one_level(vaddr@, self.pt_mem@.root(), 0, level as nat);
                assert(pte.spec_valid() && !pte.spec_huge());
                assert(ptes2 == ptes1.add(seq![ptes2.last()]));
            }

            level += 1;
            base = pte.addr();
            idx = self.constants.arch.pte_index(vaddr, level);
            val = self.pt_mem.read(base, idx);
            pte = PTE::from_u64(val);

            proof {
                assert(ptes2.last() == pte);
            }
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
            self.lemma_spec_walk_consistent_with_recursive_visit(self.pt_mem@.root(), 0, vaddr@);
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
        // TODO: add proof
        assume(false);
        let level = self.constants.arch.level_of_frame_size(frame.size);
        let huge = level < self.constants.arch.level_count() - 1;
        self.insert(vbase, level, PTE::new(frame.base, frame.attr, huge))
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
        // TODO: add proof
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
        let entries = Seq::new(
            self.spec_arch().entry_count(level),
            |i|
                {
                    let pte = PTE::spec_from_u64(self.pt_mem@.read(base, i as nat));
                    if pte.spec_valid() {
                        if level >= self.spec_arch().level_count() - 1 || pte.spec_huge() {
                            // Leaf table or block descriptor
                            NodeEntry::Frame(
                                Frame {
                                    base: pte.spec_addr(),
                                    size: self.spec_arch().frame_size(level),
                                    attr: pte.spec_attr(),
                                },
                            )
                        } else {
                            // Table descriptor, recursively build node
                            NodeEntry::Node(self.build_node(pte.spec_addr(), level + 1))
                        }
                    } else {
                        NodeEntry::Empty
                    }
                },
        );
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
        decreases self.spec_arch().level_count() - level,
    {
        let node = self.build_node(base, level);
        assert(node.constants.arch.valid());
        assert(node.level < node.constants.arch.level_count());
        // TODO: why can't Verus prove this?
        assume(node.entries.len() == self.spec_arch().entry_count(level));

        assert forall|i| 0 <= i < node.entries.len() implies {
            &&& PTTreeNode::is_entry_valid(#[trigger] node.entries[i], node.level, node.constants)
            &&& node.entries[i] is Node ==> node.entries[i]->Node_0.invariants()
        } by {
            match node.entries[i] {
                NodeEntry::Frame(frame) => {
                    // TODO: why can't Verus prove this?
                    assume(frame.size == self.spec_arch().frame_size(level));
                    // TODO: add more assumptions for GenericPTE
                    assume(frame.base.aligned(frame.size.as_nat()));
                    assume(frame.base.0 >= node.constants.pmem_lb.0);
                    assume(frame.base.0 + frame.size.as_nat() <= node.constants.pmem_ub.0);
                },
                NodeEntry::Node(subnode) => {
                    let pte = PTE::spec_from_u64(self.pt_mem@.read(base, i as nat));
                    assert(self.pt_mem@.accessible(base, i as nat));
                    // TODO: why Verus can't prove this?
                    assume(pte.spec_valid());
                    assume(!pte.spec_huge());
                    assume(subnode == self.build_node(pte.spec_addr(), level + 1));
                    // Invariants ensures this
                    assert(self.pt_mem@.contains_table(pte.spec_addr()));
                    assert(self.pt_mem@.table(pte.spec_addr()).level == level + 1);
                    self.lemma_build_node_implies_invariants(pte.spec_addr(), level + 1);
                },
                NodeEntry::Empty => (),
            }
        }
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

    /// Perform a recursive specification-level page table walk starting from a given base.
    ///
    /// Terminate upon reaching an invalid or block entry, or reaching the specified stop level.
    pub open spec fn spec_walk(self, vaddr: VAddr, base: PAddr, level: nat, stop_level: nat) -> Seq<
        PTE,
    >
        recommends
            self.invariants(),
            level <= stop_level < self.spec_arch().level_count(),
            self.pt_mem@.contains_table(base),
            self.pt_mem@.table(base).level == level,
        decreases stop_level - level,
    {
        let pte = PTE::spec_from_u64(
            self.pt_mem@.read(base, self.spec_arch().pte_index(vaddr, level)),
        );
        if level < stop_level && pte.spec_valid() && !pte.spec_huge() {
            seq![pte].add(self.spec_walk(vaddr, pte.spec_addr(), level + 1, stop_level))
        } else {
            seq![pte]
        }
    }

    /// Lemma. PTE sequence returned by `spec_walk` has length between 1 and `stop_level - level + 1`.
    proof fn lemma_walk_length_bounds(self, vaddr: VAddr, base: PAddr, level: nat, stop_level: nat)
        requires
            self.invariants(),
            level <= stop_level < self.spec_arch().level_count(),
            self.pt_mem@.contains_table(base),
            self.pt_mem@.table(base).level == level,
        ensures
            1 <= self.spec_walk(vaddr, base, level, stop_level).len() <= stop_level - level + 1,
        decreases stop_level - level,
    {
        assert(self.pt_mem@.accessible(base, self.spec_arch().pte_index(vaddr, level)));
        let pte = PTE::spec_from_u64(
            self.pt_mem@.read(base, self.spec_arch().pte_index(vaddr, level)),
        );
        if level < stop_level && pte.spec_valid() && !pte.spec_huge() {
            self.lemma_walk_length_bounds(vaddr, pte.spec_addr(), level + 1, stop_level)
        } else {
            assert(self.spec_walk(vaddr, base, level, stop_level).len() == 1);
        }
    }

    /// Lemma. `spec_walk` with `stop_level + 1` extends `spec_walk` with `stop_level`
    /// by at most one valid and non-huge PTE.
    ///
    /// That is, if the last PTE from the shorter walk is valid and not a huge page,
    /// then the walk continues one more level; otherwise, the result stays the same.
    proof fn lemma_extend_walk_by_one_level(
        self,
        vaddr: VAddr,
        base: PAddr,
        level: nat,
        stop_level: nat,
    )
        requires
            self.invariants(),
            level <= stop_level < self.spec_arch().level_count() - 1,
            self.pt_mem@.contains_table(base),
            self.pt_mem@.table(base).level == level,
        ensures
            ({
                let ptes1 = self.spec_walk(vaddr, base, level, stop_level);
                let ptes2 = self.spec_walk(vaddr, base, level, stop_level + 1);
                // `ptes1` is either a prefix of `ptes2` or `ptes1` equals `ptes2` depending on
                // the last entry in `ptes1`
                ptes2 == if ptes1.last().spec_valid() && !ptes1.last().spec_huge() {
                    ptes1.add(
                        seq![
                            PTE::spec_from_u64(
                                self.pt_mem@.read(
                                    ptes1.last().spec_addr(),
                                    self.spec_arch().pte_index(vaddr, level + ptes1.len()),
                                ),
                            ),
                        ],
                    )
                } else {
                    ptes1
                }
            }),
        decreases stop_level - level,
    {
        let ptes1 = self.spec_walk(vaddr, base, level, stop_level);
        let ptes2 = self.spec_walk(vaddr, base, level, stop_level + 1);
        self.lemma_walk_length_bounds(vaddr, base, level, stop_level);

        assert(self.pt_mem@.accessible(base, self.spec_arch().pte_index(vaddr, level)));
        // Page table entry at current level
        let pte = PTE::spec_from_u64(
            self.pt_mem@.read(base, self.spec_arch().pte_index(vaddr, level)),
        );
        if level == stop_level {
            // Base case: reached the stop level
            assert(ptes1 == seq![pte]);
            if pte.spec_valid() && !pte.spec_huge() {
                let ptes3 = self.spec_walk(vaddr, pte.spec_addr(), level + 1, stop_level + 1);
                assert(ptes2 == seq![pte].add(ptes3));
                assert(ptes3 == seq![
                    PTE::spec_from_u64(
                        self.pt_mem@.read(
                            pte.spec_addr(),
                            self.spec_arch().pte_index(vaddr, level + ptes1.len()),
                        ),
                    ),
                ])
            }
        } else {
            // Recursive case: walk down the page table
            if pte.spec_valid() && !pte.spec_huge() {
                // `ptes3` is a suffix of `ptes1`
                let ptes3 = self.spec_walk(vaddr, pte.spec_addr(), level + 1, stop_level);
                self.lemma_walk_length_bounds(vaddr, pte.spec_addr(), level + 1, stop_level);
                assert(ptes1 == seq![pte].add(ptes3));
                // `ptes4` is a suffix of `ptes2`
                let ptes4 = self.spec_walk(vaddr, pte.spec_addr(), level + 1, stop_level + 1);
                self.lemma_walk_length_bounds(vaddr, pte.spec_addr(), level + 1, stop_level + 1);
                assert(ptes2 == seq![pte].add(ptes4));
                // Recursive lemma shows the relationship between `ptes3` and `ptes4`
                self.lemma_extend_walk_by_one_level(vaddr, pte.spec_addr(), level + 1, stop_level);
                // Thus `ptes1` and `ptes2` have the same relationship
                assert(ptes2 == if ptes1.last().spec_valid() && !ptes1.last().spec_huge() {
                    ptes1.add(
                        seq![
                            PTE::spec_from_u64(
                                self.pt_mem@.read(
                                    ptes1.last().spec_addr(),
                                    self.spec_arch().pte_index(vaddr, level + ptes1.len()),
                                ),
                            ),
                        ],
                    )
                } else {
                    ptes1
                });
            }
        }
    }

    /// Lemma: Once `spec_walk` reaches a point where the last entry is invalid or huge,
    /// the walk result does not change by increasing `stop_level` further.
    proof fn lemma_full_walk_stabilizes(
        self,
        vaddr: VAddr,
        base: PAddr,
        level: nat,
        stop_level: nat,
        stop_level2: nat,
    )
        requires
            self.invariants(),
            level <= stop_level < stop_level2 < self.spec_arch().level_count(),
            self.pt_mem@.contains_table(base),
            self.pt_mem@.table(base).level == level,
        ensures
            ({
                let ptes1 = self.spec_walk(vaddr, base, level, stop_level);
                let ptes2 = self.spec_walk(vaddr, base, level, stop_level2);
                (!ptes1.last().spec_valid() || ptes1.last().spec_huge()) ==> ptes1 == ptes2
            }),
        decreases stop_level2 - stop_level,
    {
        self.lemma_extend_walk_by_one_level(vaddr, base, level, stop_level);
        if stop_level < stop_level2 - 1 {
            let ptes1 = self.spec_walk(vaddr, base, level, stop_level);
            let ptes2 = self.spec_walk(vaddr, base, level, stop_level + 1);
            if !ptes1.last().spec_valid() || ptes1.last().spec_huge() {
                assert(ptes1 == ptes2);
                self.lemma_full_walk_stabilizes(vaddr, base, level, stop_level + 1, stop_level2)
            }
        }
    }

    /// Lemma. The specification-level walk yields results consistent with the node model
    /// traversal via `PTTreeNode::recursive_visit`.
    proof fn lemma_spec_walk_consistent_with_recursive_visit(
        self,
        base: PAddr,
        level: nat,
        vaddr: VAddr,
    )
        requires
            self.invariants(),
            self.pt_mem@.contains_table(base),
            level == self.pt_mem@.table(base).level,
        ensures
            ({
                let stop_level = (self.spec_arch().level_count() - 1) as nat;
                let ptes = self.spec_walk(vaddr, base, level, stop_level);
                let pte = ptes.last();

                let node = self.build_node(base, level);
                let path = PTTreePath::from_vaddr(
                    vaddr,
                    self.spec_arch(),
                    level,
                    stop_level as nat,
                );
                let visited = node.recursive_visit(path);
                // This last entry returned by `recursive_visit` is consistent with
                // the page table entry returned by `spec_walk`.
                visited.len() == ptes.len() && visited.last() == if pte.spec_valid() {
                    NodeEntry::Frame(
                        Frame {
                            base: pte.spec_addr(),
                            size: self.spec_arch().frame_size((level + ptes.len() - 1) as nat),
                            attr: pte.spec_attr(),
                        },
                    )
                } else {
                    NodeEntry::Empty
                }
            }),
        decreases self.spec_arch().level_count() - level,
    {
        let arch = self.spec_arch();
        let stop_level = (arch.level_count() - 1) as nat;
        let ptes = self.spec_walk(vaddr, base, level, stop_level);
        let pte = ptes.last();

        let node = self.build_node(base, level);
        self.lemma_build_node_implies_invariants(base, level);
        let path = PTTreePath::from_vaddr(vaddr, arch, level, stop_level);
        PTTreePath::lemma_from_vaddr_yields_valid_path(vaddr, arch, level, stop_level);
        // Precondition of `recursive_visit`: node.invariants and path.valid
        let visited = node.recursive_visit(path);

        let (idx, remain) = path.step();
        let entry = node.entries[idx as int];
        if path.len() <= 1 {
            // Leaf node
            assert(visited == seq![entry]);
        } else {
            // Intermediate node
            assert(self.pt_mem@.accessible(base, idx));
            let pte2 = PTE::spec_from_u64(self.pt_mem@.read(base, idx));
            match entry {
                NodeEntry::Node(subnode) => {
                    // `pte2` points to a subtable
                    let subtable_base = pte2.spec_addr();
                    // TODO: why can't Verus prove this?
                    assume(pte2.spec_valid() && !pte2.spec_huge());
                    assume(subnode == self.build_node(subtable_base, level + 1));
                    // Recursive visit from the subtable
                    self.lemma_spec_walk_consistent_with_recursive_visit(
                        subtable_base,
                        level + 1,
                        vaddr,
                    );
                    assert(pte == self.spec_walk(
                        vaddr,
                        subtable_base,
                        level + 1,
                        stop_level,
                    ).last());
                    assert(visited == seq![entry].add(subnode.recursive_visit(remain)));

                    PTTreePath::lemma_from_vaddr_step(vaddr, arch, level, stop_level);
                    assert(remain == PTTreePath::from_vaddr(vaddr, arch, level + 1, stop_level));
                },
                NodeEntry::Frame(frame) => {
                    // `pte2` points to a frame
                    // TODO: why can't Verus prove this?
                    assume(pte2.spec_valid() && pte2.spec_huge());
                    assume(frame.size == arch.frame_size(level));
                    assume(frame.base == pte.spec_addr());
                    assume(frame.attr == pte.spec_attr());
                },
                NodeEntry::Empty => {
                    // `pte2` is invalid
                    // TODO: why can't Verus prove this?
                    assume(!pte2.spec_valid());
                },
            }
        }
    }

    /// Axiom. The interpreted view of the page table memory is consistent with the view derived
    /// from the model tree, ensuring semantic agreement between hardware and software views.
    #[verifier::external_body]
    pub proof fn model_consistent_with_hardware(self)
        requires
            self.invariants(),
        ensures
            self.view().view() == PageTableState::new(self.pt_mem@.interpret(), self.constants@),
    {
    }
}

} // verus!
