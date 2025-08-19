//! Spec-mode page table implementation.
use std::marker::PhantomData;
use vstd::prelude::*;

use super::pte::GenericPTE;
use crate::{
    common::{
        addr::{PAddr, VAddr},
        frame::{Frame, MemAttr},
        PagingResult,
    },
    imp::tree::{
        model::PTTreeModel,
        node::{NodeEntry, PTTreeNode},
        path::PTTreePath,
    },
    spec::{
        memory::PageTableMem,
        page_table::{PTConstants, PageTableState},
    },
};

verus! {

// Use page table memory related lemmas.
broadcast use crate::spec::memory::group_pt_mem_lemmas;

/// Spec-mode page table implementation.
pub struct PageTable<PTE: GenericPTE> {
    /// Page table memory.
    pub pt_mem: PageTableMem,
    /// Page table config constants.
    pub constants: PTConstants,
    /// Phantom data.
    pub _phantom: PhantomData<PTE>,
}

impl<PTE> PageTable<PTE> where PTE: GenericPTE {
    /// Wrap a page table memory and constants into a spec-mode page table.
    pub open spec fn new(pt_mem: PageTableMem, constants: PTConstants) -> Self {
        Self { pt_mem, constants, _phantom: PhantomData }
    }

    /// If `pte` points to a frame.
    pub open spec fn pte_points_to_frame(self, pte: PTE, level: nat) -> bool {
        pte.spec_valid() && if level < self.constants.arch.level_count() - 1 {
            pte.spec_huge()
        } else {
            !pte.spec_huge()
        }
    }

    /// If `pte` points to a table.
    pub open spec fn pte_points_to_table(self, pte: PTE, level: nat) -> bool {
        pte.spec_valid() && level < self.constants.arch.level_count() - 1 && !pte.spec_huge()
    }

    /// If `pte` points to a frame with valid address and size.
    pub open spec fn pte_valid_frame(self, pte: PTE, level: nat) -> bool {
        let frame_size = self.constants.arch.frame_size(level);
        &&& self.pte_points_to_frame(pte, level)
        &&& pte.spec_addr().aligned(frame_size.as_nat())
        &&& self.constants.pmem_lb.0 <= pte.spec_addr().0
        &&& pte.spec_addr().0 + frame_size.as_nat() <= self.constants.pmem_ub.0
    }

    /// Construct a `Frame` from a `PTE`.
    pub open spec fn pte_to_frame(self, pte: PTE, level: nat) -> Frame {
        Frame {
            base: pte.spec_addr(),
            attr: pte.spec_attr(),
            size: self.constants.arch.frame_size(level),
        }
    }

    /// If all pte in a table are invalid.
    pub open spec fn is_table_empty(self, base: PAddr) -> bool
        recommends
            self.invariants(),
            self.pt_mem.contains_table(base),
    {
        let level = self.pt_mem.table(base).level;
        forall|idx: nat|
            #![auto]
            idx < self.constants.arch.entry_count(level) ==> !PTE::spec_from_u64(
                self.pt_mem.read(base, idx),
            ).spec_valid()
    }

    /// Invariants that ensure the page table is well-formed.
    pub open spec fn invariants(self) -> bool {
        // Architecture
        &&& self.pt_mem.arch
            == self.constants.arch
        // Page table memory invariants
        &&& self.pt_mem.invariants()
        // For each page table entry that can be accessed
        &&& forall|base: PAddr, idx: nat|
            self.pt_mem.accessible(base, idx) ==> {
                let pt_mem = self.pt_mem;
                let table = pt_mem.table(base);
                let pte = PTE::spec_from_u64(pt_mem.read(base, idx));
                // If `pte` is valid and points to a table, then `pt_mem` contains the table,
                // and the table level is one level higher than `base`
                &&& self.pte_points_to_table(pte, table.level) ==> {
                    &&& pt_mem.contains_table(pte.spec_addr())
                    &&& pt_mem.table(pte.spec_addr()).level == table.level + 1
                }
                // If `table` is a leaf table, `pte` is either invalid or points to a frame
                &&& (table.level == self.constants.arch.level_count() - 1 && pte.spec_valid())
                    ==> !pte.spec_huge()
            }
            // For each 2 page table entries that can be accessed
        &&& forall|base1: PAddr, idx1: nat, base2: PAddr, idx2: nat|
            self.pt_mem.accessible(base1, idx1) && self.pt_mem.accessible(base2, idx2) ==> {
                let pte1 = PTE::spec_from_u64(self.pt_mem.read(base1, idx1));
                let pte2 = PTE::spec_from_u64(self.pt_mem.read(base2, idx2));
                // If two pte points to the same table, they must be equal
                ({
                    &&& self.pte_points_to_table(pte1, self.pt_mem.table(base1).level)
                    &&& self.pte_points_to_table(pte2, self.pt_mem.table(base2).level)
                }) ==> {
                    ||| base1 == base2 && idx1 == idx2
                    ||| (pte1.spec_addr() != pte2.spec_addr())
                }
            }
    }

    /// Recursively construct a `PTTreeNode` from a subtable.
    pub open spec fn construct_node(self, base: PAddr, level: nat) -> PTTreeNode
        recommends
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
    ;

    /// Illustrate the refinement relationship between `PageTable` and `PTTreeModel`.
    #[verifier::external_body]
    pub proof fn construct_node_facts(self, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
        ensures
            ({
                let node = self.construct_node(base, level);
                &&& node.level == level
                &&& node.constants == self.constants
                &&& node.entries.len() == self.constants.arch.entry_count(level)
                &&& forall|idx: nat|
                    idx < self.constants.arch.entry_count(level) ==> {
                        let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
                        let entry = #[trigger] node.entries[idx as int];
                        match entry {
                            NodeEntry::Frame(frame) => {
                                &&& self.pte_points_to_frame(pte, level)
                                &&& frame.base == pte.spec_addr()
                                &&& frame.attr == pte.spec_attr()
                                &&& frame.size == self.constants.arch.frame_size(level)
                            },
                            NodeEntry::Node(subnode) => {
                                &&& self.pte_points_to_table(pte, level)
                                &&& subnode == self.construct_node(pte.spec_addr(), level + 1)
                            },
                            NodeEntry::Empty => !pte.spec_valid(),
                        }
                    }
            }),
    {
    }

    /// View the page table implementation as a tree-model abstraction.
    pub open spec fn view(self) -> PTTreeModel
        recommends
            self.invariants(),
    {
        PTTreeModel { root: self.construct_node(self.pt_mem.root(), 0) }
    }

    /// Perform a recursive specification-level page table walk starting from a given base.
    ///
    /// Terminate upon reaching an invalid or block entry, or reaching the leaf level.
    pub open spec fn walk(self, vaddr: VAddr, base: PAddr, level: nat) -> (PTE, nat)
        recommends
            self.invariants(),
            self.pt_mem.contains_table(base),
            self.pt_mem.table(base).level == level,
            level < self.constants.arch.level_count(),
        decreases self.constants.arch.level_count() - level,
    {
        let pte = PTE::spec_from_u64(
            self.pt_mem.read(base, self.constants.arch.pte_index(vaddr, level)),
        );
        if self.pte_points_to_table(pte, level) {
            self.walk(vaddr, pte.spec_addr(), level + 1)
        } else {
            (pte, level)
        }
    }

    /// Perform a recursive specification-level page table insertion starting from a given base.
    pub open spec fn insert(
        self,
        vbase: VAddr,
        base: PAddr,
        level: nat,
        target_level: nat,
        new_pte: PTE,
    ) -> (Self, PagingResult)
        recommends
            self.invariants(),
            self.pt_mem.contains_table(base),
            self.pt_mem.table(base).level == level,
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
        decreases target_level - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
        if level >= target_level {
            // Insert at current level
            if pte.spec_valid() {
                (self, Err(()))
            } else {
                (
                    Self::new(self.pt_mem.write(base, idx, new_pte.spec_to_u64()), self.constants),
                    Ok(()),
                )
            }
        } else {
            if pte.spec_valid() {
                if pte.spec_huge() {
                    (self, Err(()))
                } else {
                    // Insert at next level
                    self.insert(vbase, pte.spec_addr(), level + 1, target_level, new_pte)
                }
            } else {
                // Insert intermediate table
                // Allocate a new table
                let (pt_mem, table) = self.pt_mem.alloc_table(level + 1);
                // Write entry
                let pt_mem = pt_mem.write(
                    base,
                    idx,
                    PTE::spec_new(table.base, MemAttr::spec_default(), false).spec_to_u64(),
                );
                Self::new(pt_mem, self.constants).insert(
                    vbase,
                    table.base,
                    level + 1,
                    target_level,
                    new_pte,
                )
            }
        }
    }

    /// Perform a recursive specification-level page table removal starting from a given base.
    pub open spec fn remove(self, vbase: VAddr, base: PAddr, level: nat) -> (Self, PagingResult)
        recommends
            self.invariants(),
            self.pt_mem.contains_table(base),
            self.pt_mem.table(base).level == level,
            level < self.constants.arch.level_count(),
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
        if pte.spec_valid() {
            if level >= self.constants.arch.level_count() - 1 {
                // Leaf node
                if vbase.aligned(self.constants.arch.frame_size(level).as_nat()) {
                    (
                        Self::new(
                            self.pt_mem.write(base, idx, PTE::spec_empty().spec_to_u64()),
                            self.constants,
                        ),
                        Ok(()),
                    )
                } else {
                    (self, Err(()))
                }
            } else {
                // Intermediate node
                if pte.spec_huge() {
                    if vbase.aligned(self.constants.arch.frame_size(level).as_nat()) {
                        (
                            Self::new(
                                self.pt_mem.write(base, idx, PTE::spec_empty().spec_to_u64()),
                                self.constants,
                            ),
                            Ok(()),
                        )
                    } else {
                        (self, Err(()))
                    }
                } else {
                    self.remove(vbase, pte.spec_addr(), level + 1)
                }
            }
        } else {
            (self, Err(()))
        }
    }

    /// Recursively remove empty tables along `vaddr` from `base`.
    pub open spec fn prune(self, vaddr: VAddr, base: PAddr, level: nat) -> Self
        recommends
            self.invariants(),
            self.pt_mem.contains_table(base),
            self.pt_mem.table(base).level == level,
            level < self.constants.arch.level_count(),
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
        if level >= self.constants.arch.level_count() - 1 {
            // Leaf table
            self
        } else {
            if pte.spec_valid() && !pte.spec_huge() {
                // Recycle from subtable
                let s2 = self.prune(vaddr, pte.spec_addr(), level + 1);
                if s2.is_table_empty(pte.spec_addr()) {
                    // If subtable is empty, deallocate it and mark the entry as invalid
                    Self::new(
                        s2.pt_mem.dealloc_table(pte.spec_addr()).write(
                            base,
                            idx,
                            PTE::spec_empty().spec_to_u64(),
                        ),
                        self.constants,
                    )
                } else {
                    s2
                }
            } else {
                self
            }
        }
    }

    /// Lemma. Constructing a node from memory with a valid table results in a
    /// structurally invariant model node.
    pub proof fn lemma_construct_node_implies_invariants(self, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
        ensures
            self.construct_node(base, level).invariants(),
        decreases self.constants.arch.level_count() - level,
    {
        let node = self.construct_node(base, level);
        self.construct_node_facts(base, level);

        assert forall|i| 0 <= i < node.entries.len() implies {
            &&& PTTreeNode::is_entry_valid(#[trigger] node.entries[i], node.level, node.constants)
            &&& node.entries[i] is Node ==> node.entries[i]->Node_0.invariants()
        } by {
            assert(self.pt_mem.accessible(base, i as nat));
            match node.entries[i] {
                NodeEntry::Frame(frame) => {
                    // TODO: add more assumptions for GenericPTE
                    assume({
                        &&& frame.base.aligned(frame.size.as_nat())
                        &&& frame.base.0 >= node.constants.pmem_lb.0
                        &&& frame.base.0 + frame.size.as_nat() <= node.constants.pmem_ub.0
                    });
                },
                NodeEntry::Node(subnode) => {
                    let pte = PTE::spec_from_u64(self.pt_mem.read(base, i as nat));
                    assert(self.pt_mem.accessible(base, i as nat));
                    // Invariants ensures this
                    assert(self.pt_mem.contains_table(pte.spec_addr()));
                    assert(self.pt_mem.table(pte.spec_addr()).level == level + 1);
                    self.construct_node_facts(pte.spec_addr(), level + 1);
                    self.lemma_construct_node_implies_invariants(pte.spec_addr(), level + 1);
                },
                NodeEntry::Empty => (),
            }
        }
    }

    /// Lemma. The tree model derived from the executable page table maintains the
    /// required invariants.
    pub proof fn lemma_view_implies_invariants(self)
        requires
            self.invariants(),
        ensures
            self@.invariants(),
    {
        self.pt_mem.lemma_contains_root();
        self.lemma_construct_node_implies_invariants(self.pt_mem.root(), 0);
        // TODO: fully_populated not checked
        assume(false);
    }

    /// Lemma. Empty table --construct_node--> empty node.
    pub proof fn lemma_empty_table_constructs_empty_node(self, base: PAddr)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
        ensures
            self.is_table_empty(base) <==> self.construct_node(
                base,
                self.pt_mem.table(base).level,
            ).empty(),
    {
        let level = self.pt_mem.table(base).level;
        let node = self.construct_node(base, level);
        self.construct_node_facts(base, level);
        if node.empty() {
            assert forall|idx: nat|
                #![auto]
                idx < self.constants.arch.entry_count(level) implies !PTE::spec_from_u64(
                self.pt_mem.read(base, idx),
            ).spec_valid() by {
                assert(node.entries.contains(node.entries[idx as int]));
            }
        }
    }

    /// Lemma. The specification-level walk is consistent with the node model traversal
    /// via `PTTreeNode::visit`.
    pub proof fn lemma_walk_consistent_with_model(self, vaddr: VAddr, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
        ensures
            ({
                let (pte, level2) = self.walk(vaddr, base, level);
                let node = self.construct_node(base, level);
                let path = PTTreePath::from_vaddr(
                    vaddr,
                    self.constants.arch,
                    level,
                    (self.constants.arch.level_count() - 1) as nat,
                );
                let visited = node.visit(path);
                // This last entry returned by `visit` is consistent with
                // the page table entry returned by `spec_walk`.
                level2 == level + visited.len() - 1 && visited.last() == if pte.spec_valid() {
                    NodeEntry::Frame(self.pte_to_frame(pte, level2))
                } else {
                    NodeEntry::Empty
                }
            }),
        decreases self.constants.arch.level_count() - level,
    {
        let (pte, level2) = self.walk(vaddr, base, level);
        let node = self.construct_node(base, level);
        self.construct_node_facts(base, level);

        let arch = self.constants.arch;
        let end = (arch.level_count() - 1) as nat;
        let path = PTTreePath::from_vaddr(vaddr, arch, level, end);
        // Precondition of `visit`: node.invariants and path.valid
        self.lemma_construct_node_implies_invariants(base, level);
        let visited = node.visit(path);

        let (idx, remain) = path.step();
        let entry = node.entries[idx as int];
        assert(self.pt_mem.accessible(base, idx));

        if path.len() <= 1 {
            assert(visited == seq![entry]);
        } else {
            if let NodeEntry::Node(subnode) = entry {
                let pte2 = PTE::spec_from_u64(self.pt_mem.read(base, idx));
                // `pte2` points to a subtable
                let subtable_base = pte2.spec_addr();
                // Recursive visit from the subtable
                self.lemma_walk_consistent_with_model(vaddr, subtable_base, level + 1);
                PTTreePath::lemma_from_vaddr_step(vaddr, arch, level, end);
            }
        }
    }

    /// Lemma. Allocating an intermediate table preserves invariants.
    pub proof fn lemma_alloc_intermediate_table_preserves_invariants(
        self,
        base: PAddr,
        level: nat,
        idx: nat,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level + 1 < self.constants.arch.level_count(),
            self.pt_mem.accessible(base, idx),
            !PTE::spec_from_u64(self.pt_mem.read(base, idx)).spec_valid(),
        ensures
            ({
                let (pt_mem, table) = self.pt_mem.alloc_table(level + 1);
                let pt_mem = pt_mem.write(
                    base,
                    idx,
                    PTE::spec_new(table.base, MemAttr::spec_default(), false).spec_to_u64(),
                );
                Self::new(pt_mem, self.constants).invariants()
            }),
    {
        broadcast use super::pte::group_pte_lemmas;

        let (pt_mem, table) = self.pt_mem.alloc_table(level + 1);
        let pt_mem = pt_mem.write(
            base,
            idx,
            PTE::spec_new(table.base, MemAttr::spec_default(), false).spec_to_u64(),
        );
        let s2 = Self::new(pt_mem, self.constants);

        assert forall|base2: PAddr, idx2: nat| pt_mem.accessible(base2, idx2) implies {
            let table2 = pt_mem.table(base2);
            let pte = PTE::spec_from_u64(pt_mem.read(base2, idx2));
            &&& self.pte_points_to_table(pte, table2.level) ==> {
                &&& pt_mem.contains_table(pte.spec_addr())
                &&& pt_mem.table(pte.spec_addr()).level == table2.level + 1
            }
            &&& (table2.level == self.constants.arch.level_count() - 1 && pte.spec_valid())
                ==> !pte.spec_huge()
        } by {
            let table2 = pt_mem.table(base2);
            let val = pt_mem.read(base2, idx2);
            let pte = PTE::spec_from_u64(val);

            if base2 == base && idx2 == idx {
                // `(base2, idx2)` is the entry just inserted
                PTE::lemma_eq_by_u64(
                    pte,
                    PTE::spec_new(table.base, MemAttr::spec_default(), false),
                );
            } else {
                if base2 == table.base {
                    // `base2` is the newly allocated table
                    assert(pte == PTE::spec_from_u64(0));
                } else {
                    // Entry at `(base2, idx2)` is not updated
                    assert(self.pt_mem.accessible(base2, idx2));
                    assert(val == self.pt_mem.read(base2, idx2));
                    if self.pte_points_to_table(pte, table2.level) {
                        assert(pt_mem.contains_table(pte.spec_addr()));
                        assert(pt_mem.table(pte.spec_addr()).level == table2.level + 1);
                    }
                    if table2.level == self.constants.arch.level_count() - 1 && pte.spec_valid() {
                        assert(!pte.spec_huge());
                    }
                }
            }
        }
        assert forall|base1: PAddr, idx1: nat, base2: PAddr, idx2: nat|
            pt_mem.accessible(base1, idx1) && pt_mem.accessible(base2, idx2) implies {
            let pte1 = PTE::spec_from_u64(pt_mem.read(base1, idx1));
            let pte2 = PTE::spec_from_u64(pt_mem.read(base2, idx2));
            ({
                &&& s2.pte_points_to_table(pte1, pt_mem.table(base1).level)
                &&& s2.pte_points_to_table(pte2, pt_mem.table(base2).level)
            }) ==> {
                ||| base1 == base2 && idx1 == idx2
                ||| (pte1.spec_addr() != pte2.spec_addr())
            }
        } by {
            let pte1 = PTE::spec_from_u64(pt_mem.read(base1, idx1));
            let pte2 = PTE::spec_from_u64(pt_mem.read(base2, idx2));
            if s2.pte_points_to_table(pte1, pt_mem.table(base1).level) && s2.pte_points_to_table(
                pte2,
                pt_mem.table(base2).level,
            ) {
                assert(base1 != table.base && base2 != table.base);
                assert(self.pt_mem.accessible(base1, idx1));
                assert(self.pt_mem.accessible(base2, idx2));
            }
        }
    }

    /// Lemma. `insert` does not affect existing tables.
    pub proof fn lemma_insert_preserves_old_tables(
        self,
        vbase: VAddr,
        base: PAddr,
        level: nat,
        target_level: nat,
        new_pte: PTE,
        base2: PAddr,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
            self.pt_mem.contains_table(base2),
        ensures
            self.insert(vbase, base, level, target_level, new_pte).0.pt_mem.contains_table(base2),
            self.insert(vbase, base, level, target_level, new_pte).0.pt_mem.table(base2)
                == self.pt_mem.table(base2),
        decreases target_level - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if level < target_level {
            if pte.spec_valid() {
                if !pte.spec_huge() {
                    self.lemma_insert_preserves_invariants(
                        vbase,
                        pte.spec_addr(),
                        level + 1,
                        target_level,
                        new_pte,
                    );
                    self.lemma_insert_preserves_old_tables(
                        vbase,
                        pte.spec_addr(),
                        level + 1,
                        target_level,
                        new_pte,
                        base2,
                    )
                }
            } else {
                let (pt_mem, table) = self.pt_mem.alloc_table(level + 1);
                let pt_mem = pt_mem.write(
                    base,
                    idx,
                    PTE::spec_new(table.base, MemAttr::spec_default(), false).spec_to_u64(),
                );
                self.lemma_alloc_intermediate_table_preserves_invariants(base, level, idx);
                // Ensures `pt_mem` after `alloc_table` satisfies the invariants
                Self::new(pt_mem, self.constants).lemma_insert_preserves_old_tables(
                    vbase,
                    table.base,
                    level + 1,
                    target_level,
                    new_pte,
                    base2,
                );
            }
        }
    }

    /// Lemma. `insert` does not change the root of the page table.
    pub proof fn lemma_insert_preserves_root(
        self,
        vbase: VAddr,
        base: PAddr,
        level: nat,
        target_level: nat,
        new_pte: PTE,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
        ensures
            self.insert(vbase, base, level, target_level, new_pte).0.pt_mem.root()
                == self.pt_mem.root(),
        decreases target_level - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if level < target_level {
            if pte.spec_valid() {
                if !pte.spec_huge() {
                    // Recursively insert into the next table
                    self.lemma_insert_preserves_root(
                        vbase,
                        pte.spec_addr(),
                        level + 1,
                        target_level,
                        new_pte,
                    )
                }
            } else {
                // Allocate intermediate table
                let (pt_mem, table) = self.pt_mem.alloc_table(level + 1);
                let pt_mem = pt_mem.write(
                    base,
                    idx,
                    PTE::spec_new(table.base, MemAttr::spec_default(), false).spec_to_u64(),
                );
                // `s2` is the state after allocating an intermediate table
                let s2 = Self::new(pt_mem, self.constants);

                self.lemma_alloc_intermediate_table_preserves_invariants(base, level, idx);
                assert(s2.invariants());
                s2.lemma_insert_preserves_root(vbase, table.base, level + 1, target_level, new_pte)
            }
        }
    }

    /// Lemma. Inserting an entry using `insert` preserves the page table invariants.
    pub proof fn lemma_insert_preserves_invariants(
        self,
        vbase: VAddr,
        base: PAddr,
        level: nat,
        target_level: nat,
        new_pte: PTE,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
        ensures
            self.insert(vbase, base, level, target_level, new_pte).0.constants == self.constants,
            self.insert(vbase, base, level, target_level, new_pte).0.invariants(),
        decreases target_level - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if level < target_level {
            if pte.spec_valid() {
                if !pte.spec_huge() {
                    // Recursively insert into the next table
                    self.lemma_insert_preserves_invariants(
                        vbase,
                        pte.spec_addr(),
                        level + 1,
                        target_level,
                        new_pte,
                    )
                }
            } else {
                // Allocate intermediate table
                let (pt_mem, table) = self.pt_mem.alloc_table(level + 1);
                let pt_mem = pt_mem.write(
                    base,
                    idx,
                    PTE::spec_new(table.base, MemAttr::spec_default(), false).spec_to_u64(),
                );
                // `s2` is the state after allocating an intermediate table
                let s2 = Self::new(pt_mem, self.constants);

                self.lemma_alloc_intermediate_table_preserves_invariants(base, level, idx);
                assert(s2.invariants());
                s2.lemma_insert_preserves_invariants(
                    vbase,
                    table.base,
                    level + 1,
                    target_level,
                    new_pte,
                );
            }
        }
    }

    /// Lemma. When `insert` allocates an intermediate table, the result must succeed (`Ok`).
    pub proof fn lemma_insert_intermediate_node_results_ok(
        self,
        vbase: VAddr,
        base: PAddr,
        level: nat,
        target_level: nat,
        new_pte: PTE,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
        ensures
            ({
                let idx = self.constants.arch.pte_index(vbase, level);
                let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
                level < target_level && !pte.spec_valid() ==> self.insert(
                    vbase,
                    base,
                    level,
                    target_level,
                    new_pte,
                ).1 is Ok
            }),
        decreases target_level - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
        if level < target_level && !pte.spec_valid() {
            // Allocate intermediate table
            let (pt_mem, table) = self.pt_mem.alloc_table(level + 1);
            let pt_mem = pt_mem.write(
                base,
                idx,
                PTE::spec_new(table.base, MemAttr::spec_default(), false).spec_to_u64(),
            );
            // `s2` is the state after allocating an intermediate table
            let s2 = Self::new(pt_mem, self.constants);
            self.lemma_alloc_intermediate_table_preserves_invariants(base, level, idx);
            assert(s2.invariants());

            let (_, insert_res) = s2.insert(vbase, table.base, level + 1, target_level, new_pte);
            let idx = s2.constants.arch.pte_index(vbase, level + 1);
            let pte = PTE::spec_from_u64(s2.pt_mem.read(table.base, idx));
            // New table is empty
            assert(s2.pt_mem.read(table.base, idx) == 0);
            assert(!pte.spec_valid());

            // Recursive proof for the next level
            s2.lemma_insert_intermediate_node_results_ok(
                vbase,
                table.base,
                level + 1,
                target_level,
                new_pte,
            );
        }
    }

    /// Lemma. The implementation-level insertion is consistent with the tree model.
    pub proof fn lemma_insert_consistent_with_model(
        self,
        vbase: VAddr,
        base: PAddr,
        level: nat,
        target_level: nat,
        new_pte: PTE,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level <= target_level < self.constants.arch.level_count(),
            self.pte_valid_frame(new_pte, target_level),
        ensures
            ({
                let (s2, res) = self.insert(vbase, base, level, target_level, new_pte);
                let node = self.construct_node(base, level);
                let node2 = s2.construct_node(base, level);
                let path = PTTreePath::from_vaddr(vbase, self.constants.arch, level, target_level);
                (node2, res) == node.insert(path, self.pte_to_frame(new_pte, target_level))
            }),
        decreases target_level - level,
    {
        broadcast use super::pte::group_pte_lemmas;

        let new_frame = self.pte_to_frame(new_pte, target_level);
        let (s2, res) = self.insert(vbase, base, level, target_level, new_pte);
        self.lemma_insert_preserves_invariants(vbase, base, level, target_level, new_pte);
        self.lemma_insert_preserves_old_tables(vbase, base, level, target_level, new_pte, base);

        let node = self.construct_node(base, level);
        let node2 = s2.construct_node(base, level);
        self.construct_node_facts(base, level);
        s2.construct_node_facts(base, level);

        let arch = self.constants.arch;
        let path = PTTreePath::from_vaddr(vbase, arch, level, target_level);
        self.lemma_construct_node_implies_invariants(base, level);
        s2.lemma_construct_node_implies_invariants(base, level);

        let (idx, remain) = path.step();
        let entry = node.entries[idx as int];
        assert(self.pt_mem.accessible(base, idx));
        let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));

        let right = node.insert(path, new_frame).0;
        node.lemma_insert_preserves_invariants(path, new_frame);

        if level >= target_level {
            if !pte.spec_valid() {
                PTE::lemma_eq_by_u64(PTE::spec_from_u64(s2.pt_mem.read(base, idx)), new_pte);
                // Update `pte` to `new_pte`, empty entry to frame
                assert(right == node.update(idx, NodeEntry::Frame(new_frame)));
            }
        } else {
            if pte.spec_valid() {
                if !pte.spec_huge() {
                    // `pte` points to a subtable
                    let subtable_base = pte.spec_addr();
                    let subnode: PTTreeNode = entry->Node_0;

                    let new_subnode = subnode.insert(remain, new_frame).0;
                    assert(s2 == self.insert(
                        vbase,
                        subtable_base,
                        level + 1,
                        target_level,
                        new_pte,
                    ).0);
                    // Recursive call shows subnode is updated according to model
                    self.lemma_insert_consistent_with_model(
                        vbase,
                        subtable_base,
                        level + 1,
                        target_level,
                        new_pte,
                    );
                    PTTreePath::lemma_from_vaddr_step(vbase, arch, level, target_level);
                    assert(s2.construct_node(subtable_base, level + 1) == new_subnode);
                    assert(right == node.update(idx, NodeEntry::Node(new_subnode)));

                    // The content of table `base` is unchanged
                    assert(s2.pt_mem.table_view(base) == self.pt_mem.table_view(base));
                    assert forall|i| 0 <= i < node2.entries.len() implies node2.entries[i]
                        == right.entries[i] by {
                        PTE::lemma_eq_by_u64(
                            PTE::spec_from_u64(s2.pt_mem.read(base, i as nat)),
                            PTE::spec_from_u64(self.pt_mem.read(base, i as nat)),
                        );
                        if i == idx {
                            // Entry `i` is the subtree constructed from `subtable_base`
                            assert(node2.entries[i] == NodeEntry::Node(
                                s2.construct_node(subtable_base, level + 1),
                            ));
                        } else {
                            // Other entries are unchanged
                            // TODO: pte equality not implies entry equality
                            assume(node2.entries[i] == node.entries[i]);
                        }
                    }
                }
            } else {
                let (allocated, table) = self.pt_mem.alloc_table(level + 1);
                let written = allocated.write(
                    base,
                    idx,
                    PTE::spec_new(table.base, MemAttr::spec_default(), false).spec_to_u64(),
                );
                let subtable_base = table.base;
                self.lemma_alloc_intermediate_table_preserves_invariants(base, level, idx);

                // s3 is the state after allocating a new intermediate table
                let s3 = Self::new(written, self.constants);
                let subnode = PTTreeNode::new(self.constants, level + 1);
                PTE::lemma_eq_by_u64(
                    PTE::spec_from_u64(s3.pt_mem.read(base, idx)),
                    PTE::spec_new(table.base, MemAttr::spec_default(), false),
                );
                assert(s3.construct_node(base, level).entries[idx as int] == NodeEntry::Node(
                    subnode,
                ));

                let new_subnode = subnode.insert(remain, new_frame).0;
                assert(s2 == s3.insert(vbase, table.base, level + 1, target_level, new_pte).0);
                // Recursive call shows subnode is updated according to model
                s3.lemma_insert_consistent_with_model(
                    vbase,
                    subtable_base,
                    level + 1,
                    target_level,
                    new_pte,
                );
                PTTreePath::lemma_from_vaddr_step(vbase, arch, level, target_level);
                assert(s2.construct_node(subtable_base, level + 1) == new_subnode);
                assert(right == node.update(idx, NodeEntry::Node(new_subnode)));

                // The content of table `base` is unchanged
                assert(s2.pt_mem.table_view(base) == s3.pt_mem.table_view(base));
                assert forall|i| 0 <= i < node2.entries.len() implies node2.entries[i]
                    == right.entries[i] by {
                    if i == idx {
                        // Entry `i` is the subtree constructed from `subtable_base`
                        assert(node2.entries[i] == NodeEntry::Node(new_subnode));
                    } else {
                        // Other entries are unchanged
                        assert(node2.entries[i] == node.entries[i]);
                    }
                }
            }
        }
    }

    /// Lemma. Removing a page table entry using `remove` maintains the page table invariants.
    pub proof fn lemma_remove_preserves_invariants(self, vbase: VAddr, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
        ensures
            self.remove(vbase, base, level).0.invariants(),
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));
        if self.pte_points_to_table(pte, level) {
            self.lemma_remove_preserves_invariants(vbase, pte.spec_addr(), level + 1)
        }
    }

    /// Lemma. `remove` does not affect existing tables.
    pub proof fn lemma_remove_preserves_old_tables(
        self,
        vbase: VAddr,
        base: PAddr,
        level: nat,
        base2: PAddr,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
            self.pt_mem.contains_table(base2),
        ensures
            self.remove(vbase, base, level).0.pt_mem.contains_table(base2),
            self.remove(vbase, base, level).0.pt_mem.table(base2) == self.pt_mem.table(base2),
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));
        if self.pte_points_to_table(pte, level) {
            self.lemma_remove_preserves_old_tables(vbase, pte.spec_addr(), level + 1, base2)
        }
    }

    /// Lemma. `remove` does not change the root of the page table.
    pub proof fn lemma_remove_preserves_root(self, vbase: VAddr, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
        ensures
            self.remove(vbase, base, level).0.pt_mem.root() == self.pt_mem.root(),
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vbase, level);
        let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));
        if self.pte_points_to_table(pte, level) {
            self.lemma_remove_preserves_root(vbase, pte.spec_addr(), level + 1)
        }
    }

    /// Lemma. The implementation-level removal is consistent with the tree model.
    pub proof fn lemma_remove_consistent_with_model(self, vbase: VAddr, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
        ensures
            ({
                let (s2, res) = self.remove(vbase, base, level);
                let node = self.construct_node(base, level);
                let node2 = s2.construct_node(base, level);
                let path = PTTreePath::from_vaddr(
                    vbase,
                    self.constants.arch,
                    level,
                    (self.constants.arch.level_count() - 1) as nat,
                );
                (node2, res) == node.remove(path)
            }),
        decreases self.constants.arch.level_count() - level,
    {
        broadcast use super::pte::group_pte_lemmas;

        let s2 = self.remove(vbase, base, level).0;
        self.lemma_remove_preserves_invariants(vbase, base, level);
        self.lemma_remove_preserves_old_tables(vbase, base, level, base);

        let node = self.construct_node(base, level);
        let node2 = s2.construct_node(base, level);
        self.construct_node_facts(base, level);
        s2.construct_node_facts(base, level);

        let arch = self.constants.arch;
        let end = (arch.level_count() - 1) as nat;
        let path = PTTreePath::from_vaddr(vbase, arch, level, end);
        // Precondition of `remove`: node.invariants and path.valid
        self.lemma_construct_node_implies_invariants(base, level);
        s2.lemma_construct_node_implies_invariants(base, level);

        let (idx, remain) = path.step();
        let entry = node.entries[idx as int];
        let entry2 = node2.entries[idx as int];
        assert(self.pt_mem.accessible(base, idx));
        let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
        let pte2 = PTE::spec_from_u64(s2.pt_mem.read(base, idx));

        if path.len() <= 1 {
            match entry {
                NodeEntry::Frame(_) => {
                    // Update frame entry to empty
                    assert(s2.pt_mem == self.pt_mem.write(
                        base,
                        idx,
                        PTE::spec_empty().spec_to_u64(),
                    ));
                    PTE::lemma_eq_by_u64(pte2, PTE::spec_empty());
                    assert(entry2 == NodeEntry::Empty);
                },
                _ => (),
            }
        } else {
            match entry {
                NodeEntry::Node(subnode) => {
                    // `pte` points to a subtable
                    let subtable_base = pte.spec_addr();
                    // Recursive remove from the subtable
                    self.lemma_remove_consistent_with_model(vbase, subtable_base, level + 1);
                    PTTreePath::lemma_from_vaddr_step(vbase, arch, level, end);
                },
                NodeEntry::Frame(frame) => {
                    if path.has_zero_tail(level) {
                        assert(entry2 == NodeEntry::Empty);
                    }
                },
                NodeEntry::Empty => (),
            }
        }
    }

    /// Lemma. Deallocating an intermediate table preserves invariants.
    pub proof fn lemma_dealloc_intermediate_table_preserves_invariants(
        self,
        base: PAddr,
        level: nat,
        idx: nat,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count() - 1,
            self.pt_mem.accessible(base, idx),
            ({
                let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
                pte.spec_valid() && !pte.spec_huge() && self.is_table_empty(pte.spec_addr())
            }),
        ensures
            ({
                let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
                let pt_mem = self.pt_mem.dealloc_table(pte.spec_addr());
                let pt_mem = pt_mem.write(base, idx, PTE::spec_empty().spec_to_u64());
                Self::new(pt_mem, self.constants).invariants()
            }),
    {
        broadcast use super::pte::group_pte_lemmas;

        let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
        let pt_mem = self.pt_mem.dealloc_table(pte.spec_addr()).write(
            base,
            idx,
            PTE::spec_empty().spec_to_u64(),
        );
        let s2 = Self::new(pt_mem, self.constants);

        assert forall|base2: PAddr, idx2: nat| pt_mem.accessible(base2, idx2) implies {
            let table2 = pt_mem.table(base2);
            let pte2 = PTE::spec_from_u64(pt_mem.read(base2, idx2));
            &&& self.pte_points_to_table(pte2, table2.level) ==> {
                &&& pt_mem.contains_table(pte2.spec_addr())
                &&& pt_mem.table(pte2.spec_addr()).level == table2.level + 1
            }
            &&& (table2.level == self.constants.arch.level_count() - 1 && pte2.spec_valid())
                ==> !pte2.spec_huge()
        } by {
            let table2 = pt_mem.table(base2);
            let val = pt_mem.read(base2, idx2);
            let pte2 = PTE::spec_from_u64(val);

            if base2 == base && idx2 == idx {
                // `(base2, idx2)` is the entry we just inserted
                PTE::lemma_eq_by_u64(pte2, PTE::spec_empty());
            } else {
                assert(self.pt_mem.accessible(base2, idx2));
                PTE::lemma_eq_by_u64(pte2, PTE::spec_from_u64(self.pt_mem.read(base2, idx2)));
                if self.pte_points_to_table(pte2, table2.level) {
                    // Invariants ensures no double reference
                    assert(pte2.spec_addr() != pte.spec_addr());
                }
            }
        }
        assert forall|base1: PAddr, idx1: nat, base2: PAddr, idx2: nat|
            pt_mem.accessible(base1, idx1) && pt_mem.accessible(base2, idx2) implies {
            let pte1 = PTE::spec_from_u64(pt_mem.read(base1, idx1));
            let pte2 = PTE::spec_from_u64(pt_mem.read(base2, idx2));
            ({
                &&& s2.pte_points_to_table(pte1, pt_mem.table(base1).level)
                &&& s2.pte_points_to_table(pte2, pt_mem.table(base2).level)
            }) ==> {
                ||| base1 == base2 && idx1 == idx2
                ||| (pte1.spec_addr() != pte2.spec_addr())
            }
        } by {
            let pte1 = PTE::spec_from_u64(pt_mem.read(base1, idx1));
            let pte2 = PTE::spec_from_u64(pt_mem.read(base2, idx2));
            if s2.pte_points_to_table(pte1, pt_mem.table(base1).level) && s2.pte_points_to_table(
                pte2,
                pt_mem.table(base2).level,
            ) {
                assert(base1 != pte.spec_addr() && base2 != pte.spec_addr());
                assert(self.pt_mem.accessible(base1, idx1));
                assert(self.pt_mem.accessible(base2, idx2));
            }
        }
    }

    /// Lemma. `prune` mantains the page table invariants.
    pub proof fn lemma_prune_preserves_invariants(self, vaddr: VAddr, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
        ensures
            self.prune(vaddr, base, level).invariants(),
            self.prune(vaddr, base, level).constants == self.constants,
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if level < self.constants.arch.level_count() - 1 && pte.spec_valid() && !pte.spec_huge() {
            self.lemma_prune_preserves_invariants(vaddr, pte.spec_addr(), level + 1);
            self.lemma_prune_preserves_lower_tables(vaddr, pte.spec_addr(), level + 1, base);
            self.lemma_prune_preserves_lower_tables(
                vaddr,
                pte.spec_addr(),
                level + 1,
                pte.spec_addr(),
            );
            let s2 = self.prune(vaddr, pte.spec_addr(), level + 1);
            if s2.is_table_empty(pte.spec_addr()) {
                s2.lemma_dealloc_intermediate_table_preserves_invariants(base, level, idx);
            }
        }
    }

    /// Lemma. `prune` does not remove tables with level lower than the current level.
    pub proof fn lemma_prune_preserves_lower_tables(
        self,
        vaddr: VAddr,
        base: PAddr,
        level: nat,
        base2: PAddr,
    )
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
            self.pt_mem.contains_table(base2),
            self.pt_mem.table(base2).level <= level,
        ensures
            self.prune(vaddr, base, level).pt_mem.contains_table(base2),
            self.prune(vaddr, base, level).pt_mem.table(base2) == self.pt_mem.table(base2),
            self.pt_mem.table(base2).level < level ==> self.prune(
                vaddr,
                base,
                level,
            ).pt_mem.table_view(base2) == self.pt_mem.table_view(base2),
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if self.pte_points_to_table(pte, level) {
            self.lemma_prune_preserves_invariants(vaddr, pte.spec_addr(), level + 1);
            // `base`, `pte.spec_addr()`, `base2` are not affected after `prune`
            self.lemma_prune_preserves_lower_tables(vaddr, pte.spec_addr(), level + 1, base);
            self.lemma_prune_preserves_lower_tables(
                vaddr,
                pte.spec_addr(),
                level + 1,
                pte.spec_addr(),
            );
            self.lemma_prune_preserves_lower_tables(vaddr, pte.spec_addr(), level + 1, base2);
        }
    }

    /// Lemma. `prune` does not change the root of the page table.
    pub proof fn lemma_prune_preserves_root(self, vaddr: VAddr, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
        ensures
            self.prune(vaddr, base, level).pt_mem.root() == self.pt_mem.root(),
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));

        if self.pte_points_to_table(pte, level) {
            self.lemma_prune_preserves_invariants(vaddr, pte.spec_addr(), level + 1);
            self.lemma_prune_preserves_root(vaddr, pte.spec_addr(), level + 1);
            self.lemma_prune_preserves_lower_tables(vaddr, pte.spec_addr(), level + 1, base);
            self.lemma_prune_preserves_lower_tables(
                vaddr,
                pte.spec_addr(),
                level + 1,
                pte.spec_addr(),
            );
        }
    }

    /// Lemma. The implementation-level prune is consistent with the tree model.
    pub proof fn lemma_prune_consistent_with_model(self, vaddr: VAddr, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
        ensures
            ({
                let s2 = self.prune(vaddr, base, level);
                let node = self.construct_node(base, level);
                let node2 = s2.construct_node(base, level);
                let path = PTTreePath::from_vaddr(
                    vaddr,
                    self.constants.arch,
                    level,
                    (self.constants.arch.level_count() - 1) as nat,
                );
                node2 == node.prune(path)
            }),
        decreases self.constants.arch.level_count() - level,
    {
        broadcast use super::pte::group_pte_lemmas;

        let s2 = self.prune(vaddr, base, level);
        self.lemma_prune_preserves_invariants(vaddr, base, level);
        self.lemma_prune_preserves_lower_tables(vaddr, base, level, base);

        let node = self.construct_node(base, level);
        let node2 = s2.construct_node(base, level);
        self.construct_node_facts(base, level);
        s2.construct_node_facts(base, level);

        let arch = self.constants.arch;
        let end = (arch.level_count() - 1) as nat;
        let path = PTTreePath::from_vaddr(vaddr, arch, level, end);
        self.lemma_construct_node_implies_invariants(base, level);
        s2.lemma_construct_node_implies_invariants(base, level);

        let (idx, remain) = path.step();
        let entry = node.entries[idx as int];
        assert(self.pt_mem.accessible(base, idx));
        let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));

        let right = node.prune(path);
        node.lemma_prune_preserves_invariants(path);

        if self.pte_points_to_table(pte, level) {
            // `pte` points to a subtable
            let subtable_base = pte.spec_addr();
            let subnode: PTTreeNode = entry->Node_0;

            let s3 = self.prune(vaddr, subtable_base, level + 1);
            let new_subnode = subnode.prune(remain);
            // Recursive call shows subnode is updated according to model
            self.lemma_prune_preserves_invariants(vaddr, subtable_base, level + 1);
            self.lemma_prune_consistent_with_model(vaddr, subtable_base, level + 1);
            PTTreePath::lemma_from_vaddr_step(vaddr, arch, level, end);
            assert(s3.construct_node(subtable_base, level + 1) == new_subnode);

            // `base`, `pte.spec_addr()`, `base2` are not affected after `prune`
            self.lemma_prune_preserves_lower_tables(vaddr, subtable_base, level + 1, base);
            self.lemma_prune_preserves_lower_tables(vaddr, subtable_base, level + 1, subtable_base);
            // The content of table `base` is not affected after `prune`
            assert(s3.pt_mem.table_view(base) == self.pt_mem.table_view(base));

            s3.lemma_empty_table_constructs_empty_node(pte.spec_addr());
            if s3.is_table_empty(pte.spec_addr()) {
                // Lemma shows `new_subnode` is empty
                assert(right == node.update(idx, NodeEntry::Empty));
                assert(s2.pt_mem == s3.pt_mem.dealloc_table(subtable_base).write(
                    base,
                    idx,
                    PTE::spec_empty().spec_to_u64(),
                ));
                assert forall|i| 0 <= i < node2.entries.len() implies node2.entries[i]
                    == right.entries[i] by {
                    if i == idx {
                        // Entry `i` is empty (removed)
                        PTE::lemma_eq_by_u64(
                            PTE::spec_from_u64(s2.pt_mem.read(base, idx)),
                            PTE::spec_empty(),
                        );
                        assert(node2.entries[i] is Empty);
                    } else {
                        PTE::lemma_eq_by_u64(
                            PTE::spec_from_u64(s3.pt_mem.read(base, i as nat)),
                            PTE::spec_from_u64(self.pt_mem.read(base, i as nat)),
                        );
                        PTE::lemma_eq_by_u64(
                            PTE::spec_from_u64(s2.pt_mem.read(base, i as nat)),
                            PTE::spec_from_u64(s3.pt_mem.read(base, i as nat)),
                        );
                        // Other entries are unchanged
                        // TODO: Only ensure pte equality, not entry equality
                        assume(node2.entries[i] == node.entries[i]);
                    }
                }
                assert(node2.entries == right.entries);
            } else {
                // Lemma shows `new_subnode` is not empty
                assert(right == node.update(idx, NodeEntry::Node(new_subnode)));
                assert(s2 == s3);

                assert forall|i| 0 <= i < node2.entries.len() implies node2.entries[i]
                    == right.entries[i] by {
                    PTE::lemma_eq_by_u64(
                        PTE::spec_from_u64(s2.pt_mem.read(base, i as nat)),
                        PTE::spec_from_u64(self.pt_mem.read(base, i as nat)),
                    );
                    if i == idx {
                        // Entry `i` is the subtree constructed from `subtable_base`
                        assert(node2.entries[i] == NodeEntry::Node(new_subnode));
                    } else {
                        // Other entries are unchanged
                        // TODO: Only ensure pte equality, not entry equality
                        assume(node2.entries[i] == node.entries[i]);
                    }
                }
                assert(node2.entries == right.entries);
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
            self@@ == PageTableState::new(self.pt_mem.interpret(), self.constants),
    {
    }
}

} // verus!
