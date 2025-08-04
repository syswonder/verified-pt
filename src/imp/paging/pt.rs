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

    /// Invariants that ensure the page table is well-formed.
    pub open spec fn invariants(self) -> bool {
        // Target architecture
        &&& self.pt_mem.arch
            == self.constants.arch
        // Page table memory invariants
        &&& self.pt_mem.invariants()
        // For each table descriptor that can be accessed
        &&& forall|base: PAddr, idx: nat|
            self.pt_mem.accessible(base, idx) ==> {
                let pt_mem = self.pt_mem;
                let table = pt_mem.table(base);
                let pte = PTE::spec_from_u64(pt_mem.read(base, idx));
                // If `table` is not a leaf table, `pte` is valid and points to a table...
                // then `pt_mem` contains the table, and the table level is one level higher than `base`
                &&& ({
                    &&& table.level < self.constants.arch.level_count() - 1
                    &&& pte.spec_valid()
                    &&& !pte.spec_huge()
                }) ==> {
                    &&& pt_mem.contains_table(pte.spec_addr())
                    &&& pt_mem.table(pte.spec_addr()).level == table.level + 1
                }
                // If `table` is a leaf table, `pte` is either invalid or points to a frame
                &&& (table.level == self.constants.arch.level_count() - 1 && pte.spec_valid())
                    ==> !pte.spec_huge()
            }
    }

    /// Recursively construct a `PTTreeNode` from a subtable.
    pub open spec fn construct_node(self, base: PAddr, level: nat) -> PTTreeNode
        recommends
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
        decreases self.constants.arch.level_count() - level,
    {
        let entries = Seq::new(
            self.constants.arch.entry_count(level),
            |i|
                {
                    let pte = PTE::spec_from_u64(self.pt_mem.read(base, i as nat));
                    if pte.spec_valid() {
                        if level >= self.constants.arch.level_count() - 1 || pte.spec_huge() {
                            // Leaf table or block descriptor
                            NodeEntry::Frame(
                                Frame {
                                    base: pte.spec_addr(),
                                    size: self.constants.arch.frame_size(level),
                                    attr: pte.spec_attr(),
                                },
                            )
                        } else {
                            // Table descriptor, recursively build node
                            NodeEntry::Node(self.construct_node(pte.spec_addr(), level + 1))
                        }
                    } else {
                        NodeEntry::Empty
                    }
                },
        );
        PTTreeNode { constants: self.constants, level, entries }
    }

    /// Abstract the page table implementation into a tree-model abstraction.
    pub open spec fn view(self) -> PTTreeModel
        recommends
            self.invariants(),
    {
        PTTreeModel { root: self.construct_node(self.pt_mem.root(), 0) }
    }

    /// Check if `pte` points to a frame.
    pub open spec fn pte_points_to_frame(self, pte: PTE, level: nat) -> bool {
        pte.spec_valid() && if level == self.constants.arch.level_count() - 1 {
            !pte.spec_huge()
        } else {
            pte.spec_huge()
        }
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
        if level < self.constants.arch.level_count() - 1 && pte.spec_valid() && !pte.spec_huge() {
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
            self.pte_points_to_frame(new_pte, target_level),
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

    /// Recursively remove empty nodes along `vaddr` from `base`.
    pub open spec fn recycle(self, vaddr: VAddr, base: PAddr, level: nat) -> Self
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
            // Leaf node
            self
        } else {
            if pte.spec_valid() && !pte.spec_huge() {
                // Recycle subnode
                let s2 = self.recycle(vaddr, pte.spec_addr(), level + 1);
                if s2.pt_mem.is_table_empty(pte.spec_addr()) {
                    // If subnode is empty, deallocate the table, and mark the entry as invalid
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
        assert(node.constants.arch.valid());
        assert(node.level < node.constants.arch.level_count());
        // TODO: why can't Verus prove this?
        assume(node.entries.len() == self.constants.arch.entry_count(level));

        assert forall|i| 0 <= i < node.entries.len() implies {
            &&& PTTreeNode::is_entry_valid(#[trigger] node.entries[i], node.level, node.constants)
            &&& node.entries[i] is Node ==> node.entries[i]->Node_0.invariants()
        } by {
            match node.entries[i] {
                NodeEntry::Frame(frame) => {
                    // TODO: why can't Verus prove this?
                    assume(frame.size == self.constants.arch.frame_size(level));
                    // TODO: add more assumptions for GenericPTE
                    assume(frame.base.aligned(frame.size.as_nat()));
                    assume(frame.base.0 >= node.constants.pmem_lb.0);
                    assume(frame.base.0 + frame.size.as_nat() <= node.constants.pmem_ub.0);
                },
                NodeEntry::Node(subnode) => {
                    let pte = PTE::spec_from_u64(self.pt_mem.read(base, i as nat));
                    assert(self.pt_mem.accessible(base, i as nat));
                    // TODO: why Verus can't prove this?
                    assume(pte.spec_valid());
                    assume(!pte.spec_huge());
                    assume(subnode == self.construct_node(pte.spec_addr(), level + 1));
                    // Invariants ensures this
                    assert(self.pt_mem.contains_table(pte.spec_addr()));
                    assert(self.pt_mem.table(pte.spec_addr()).level == level + 1);
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
                    NodeEntry::Frame(
                        Frame {
                            base: pte.spec_addr(),
                            size: self.constants.arch.frame_size((level2) as nat),
                            attr: pte.spec_attr(),
                        },
                    )
                } else {
                    NodeEntry::Empty
                }
            }),
        decreases self.constants.arch.level_count() - level,
    {
        let arch = self.constants.arch;
        let (pte, level2) = self.walk(vaddr, base, level);

        let node = self.construct_node(base, level);
        let end = (arch.level_count() - 1) as nat;
        self.lemma_construct_node_implies_invariants(base, level);
        let path = PTTreePath::from_vaddr(vaddr, arch, level, end);
        PTTreePath::lemma_from_vaddr_yields_valid_path(vaddr, arch, level, end);
        // Precondition of `visit`: node.invariants and path.valid
        let visited = node.visit(path);

        let (idx, remain) = path.step();
        let entry = node.entries[idx as int];
        if path.len() <= 1 {
            // Leaf node
            assert(visited == seq![entry]);
        } else {
            // Intermediate node
            assert(self.pt_mem.accessible(base, idx));
            let pte2 = PTE::spec_from_u64(self.pt_mem.read(base, idx));
            match entry {
                NodeEntry::Node(subnode) => {
                    // `pte2` points to a subtable
                    let subtable_base = pte2.spec_addr();
                    // TODO: why can't Verus prove this?
                    assume(pte2.spec_valid() && !pte2.spec_huge());
                    assume(subnode == self.construct_node(subtable_base, level + 1));
                    // Recursive visit from the subtable
                    self.lemma_walk_consistent_with_model(vaddr, subtable_base, level + 1);
                    assert(pte == self.walk(vaddr, subtable_base, level + 1).0);
                    assert(visited == seq![entry].add(subnode.visit(remain)));

                    PTTreePath::lemma_from_vaddr_step(vaddr, arch, level, end);
                    assert(remain == PTTreePath::from_vaddr(vaddr, arch, level + 1, end));
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

    /// Lemma. The specification-level insertion is consistent with the node model
    /// insertion via `PTTreeNode::insert`.
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
            self.pte_points_to_frame(new_pte, target_level),
        ensures
            ({
                let (s2, res) = self.insert(vbase, base, level, target_level, new_pte);
                let node = self.construct_node(base, level);
                let node2 = s2.construct_node(base, level);
                let path = PTTreePath::from_vaddr(vbase, self.constants.arch, level, target_level);
                (node2, res) == node.insert(
                    path,
                    Frame {
                        base: new_pte.spec_addr(),
                        size: self.constants.arch.frame_size(target_level),
                        attr: new_pte.spec_attr(),
                    },
                )
            }),
    {
        assume(false);
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
            &&& ({
                &&& table2.level < self.constants.arch.level_count() - 1
                &&& pte.spec_valid()
                &&& !pte.spec_huge()
            }) ==> {
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
                // `(base2, idx2)` is the entry we just inserted
                PTE::lemma_eq_by_u64(
                    pte,
                    PTE::spec_new(table.base, MemAttr::spec_default(), false),
                );
                assert(pte == PTE::spec_new(table.base, MemAttr::spec_default(), false));
            } else {
                if base2 == table.base {
                    // `base2` is the newly allocated table
                    assert(pte == PTE::spec_from_u64(0));
                } else {
                    // Entry at `(base2, idx2)` is not updated
                    assert(self.pt_mem.accessible(base2, idx2));
                    assert(val == self.pt_mem.read(base2, idx2));
                    if table2.level < self.constants.arch.level_count() - 1 && pte.spec_valid()
                        && !pte.spec_huge() {
                        assert(pt_mem.contains_table(pte.spec_addr()));
                        assert(pt_mem.table(pte.spec_addr()).level == table2.level + 1);
                    }
                    if table2.level == self.constants.arch.level_count() - 1 && pte.spec_valid() {
                        assert(!pte.spec_huge());
                    }
                }
            }
        }
    }

    /// Lemma. `insert` does not change the physical root address of the page table.
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
            self.pte_points_to_frame(new_pte, target_level),
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
            self.pte_points_to_frame(new_pte, target_level),
        ensures
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
            self.pte_points_to_frame(new_pte, target_level),
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

    /// Lemma. The specification-level removal is consistent with the node model
    /// insertion via `PTTreeNode::insert`.
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
    {
        assume(false);
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
        if pte.spec_valid() && level < self.constants.arch.level_count() - 1 && !pte.spec_huge() {
            self.lemma_remove_preserves_invariants(vbase, pte.spec_addr(), level + 1)
        }
    }

    /// Lemma. `remove` does not change the physical root address of the page table.
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
        if pte.spec_valid() && level < self.constants.arch.level_count() - 1 && !pte.spec_huge() {
            self.lemma_remove_preserves_root(vbase, pte.spec_addr(), level + 1)
        }
    }

    /// Lemma. `recycle` mantains the page table invariants.
    pub proof fn lemma_recycle_preserves_invariants(self, vaddr: VAddr, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
        ensures
            self.recycle(vaddr, base, level).invariants(),
            self.recycle(vaddr, base, level).constants == self.constants,
        decreases self.constants.arch.level_count() - level,
    {
        let idx = self.constants.arch.pte_index(vaddr, level);
        let pte = PTE::spec_from_u64(self.pt_mem.read(base, idx));
        assert(self.pt_mem.accessible(base, idx));
        if level < self.constants.arch.level_count() - 1 && pte.spec_valid() && !pte.spec_huge() {
            self.lemma_recycle_preserves_invariants(vaddr, pte.spec_addr(), level + 1);
            let s2 = self.recycle(vaddr, pte.spec_addr(), level + 1);
            if s2.pt_mem.is_table_empty(pte.spec_addr()) {
                let pt_mem = s2.pt_mem.dealloc_table(pte.spec_addr()).write(
                    base,
                    idx,
                    PTE::spec_empty().spec_to_u64(),
                );
                // TODO
                assume(Self::new(pt_mem, self.constants).invariants());
            }
        }
    }

    /// Lemma. `recycle` does not remove current page table.
    pub proof fn lemma_recycle_preserves_current(self, vaddr: VAddr, base: PAddr, level: nat)
        requires
            self.invariants(),
            self.pt_mem.contains_table(base),
            level == self.pt_mem.table(base).level,
            level < self.constants.arch.level_count(),
        ensures
            self.recycle(vaddr, base, level).pt_mem.contains_table(base),
        decreases self.constants.arch.level_count() - level,
    {
        assume(false);
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
