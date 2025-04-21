//! Abstract page table tree model, provides refinement proof.
use vstd::prelude::*;

use super::{
    node::{NodeEntry, PTConfig, PTTreeNode},
    path::PTTreePath,
};
use crate::spec::{
    addr::{PAddr, VAddr},
    arch::PTArch,
    frame::Frame,
    pt_spec::{PTConstants, PageTableState},
};

verus! {

/// Page table tree model.
pub struct PTTreeModel {
    /// The root node.
    pub root: PTTreeNode,
}

impl PTTreeModel {
    /// Wrap a root node into a tree model.
    pub open spec fn new(root: PTTreeNode) -> Self {
        Self { root }
    }

    /// Create an empty page table tree.
    pub open spec fn empty(config: PTConfig) -> Self {
        Self::new(PTTreeNode::new(config, 0))
    }

    /// Invariants. The tree structure and node configurations are valid.
    pub open spec fn invariants(self) -> bool {
        &&& self.root.level == 0
        &&& self.root.invariants()
    }

    /// Get page table architecture.
    pub open spec fn arch(self) -> PTArch {
        self.root.config.arch
    }

    /// Get physical memory lower bound.
    pub open spec fn pmem_lb(self) -> PAddr {
        self.root.config.pmem_lb
    }

    /// Get physical memory upper bound.
    pub open spec fn pmem_ub(self) -> PAddr {
        self.root.config.pmem_ub
    }

    /// Interpret the tree as `(path, frame)` mappings.
    pub open spec fn path_mappings(self) -> Map<PTTreePath, Frame> {
        Map::new(
            |path: PTTreePath|
                path.valid(self.arch(), 0) && self.root.recursive_visit(path).len() == path.len()
                    && self.root.recursive_visit(path).last() is Frame,
            |path: PTTreePath| self.root.recursive_visit(path).last()->Frame_0,
        )
    }

    /// Interpret the tree as `(vbase, frame)` mappings.
    pub open spec fn mappings(self) -> Map<VAddr, Frame> {
        Map::new(
            |vbase: VAddr|
                exists|path| #[trigger]
                    self.path_mappings().contains_key(path) && path.to_vaddr(self.arch()) == vbase,
            |vbase: VAddr|
                {
                    let path = choose|path| #[trigger]
                        self.path_mappings().contains_key(path) && path.to_vaddr(self.arch())
                            == vbase;
                    self.path_mappings()[path]
                },
        )
    }

    /// View the tree as `PageTableState`.
    pub open spec fn view(self) -> PageTableState {
        PageTableState {
            mappings: self.mappings(),
            constants: PTConstants {
                arch: self.arch(),
                pmem_lb: self.pmem_lb().idx(),
                pmem_ub: self.pmem_ub().idx(),
            },
        }
    }

    /// Map a virtual address to a physical frame.
    ///
    /// If mapping succeeds, return `Ok` and the updated tree.
    pub open spec fn map(self, vbase: VAddr, frame: Frame) -> Result<Self, ()>
        recommends
            self.invariants(),
            self.arch().is_valid_frame_size(frame.size),
            vbase.aligned(frame.size.as_nat()),
            frame.base.aligned(frame.size.as_nat()),
            frame.base.0 >= self.pmem_lb().0,
            frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0,
    {
        let path = PTTreePath::from_vaddr(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        // Check if already mapped
        let visited = self.root.recursive_visit(path);
        if visited.last() is Empty {
            Ok(Self::new(self.root.recursive_insert(path, frame)))
        } else {
            Err(())
        }
    }

    /// Unmap a virtual address.
    ///
    /// If unmapping succeeds, return `Ok` and the updated tree.
    pub open spec fn unmap(self, vbase: VAddr) -> Result<Self, ()>
        recommends
            self.invariants(),
    {
        // Check if already mapped
        if let Ok((_, frame)) = self.query(vbase) {
            // `path` is the right path to the target entry
            let path = PTTreePath::from_vaddr(
                vbase,
                self.arch(),
                self.arch().level_of_frame_size(frame.size),
            );
            Ok(Self::new(self.root.recursive_remove(path)))
        } else {
            Err(())
        }
    }

    /// Query a virtual address, return the mapped physical frame.
    ///
    /// If there is no mapping for the virtual address, return `Err(())`.
    pub open spec fn query(self, vaddr: VAddr) -> Result<(VAddr, Frame), ()>
        recommends
            self.invariants(),
    {
        let path = PTTreePath::from_vaddr(
            vaddr,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        let visited = self.root.recursive_visit(path);
        match visited.last() {
            NodeEntry::Frame(frame) => Ok(
                (self.arch().vbase_of_va(vaddr, (visited.len() - 1) as nat), frame),
            ),
            _ => Err(()),
        }
    }

    /// Lemma. All `(path, frame)` mappings have valid size and alignment.
    pub proof fn lemma_path_mappings_valid(self)
        requires
            self.invariants(),
        ensures
            forall|path, frame| #[trigger]
                self.path_mappings().contains_pair(path, frame) ==> {
                    &&& frame.size == self.arch().frame_size((path.len() - 1) as nat)
                    &&& path.to_vaddr(self.arch()).aligned(frame.size.as_nat())
                    &&& frame.base.aligned(frame.size.as_nat())
                    &&& frame.base.0 >= self.pmem_lb().0
                    &&& frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0
                },
    {
        assert forall|path, frame| #[trigger]
            self.path_mappings().contains_pair(path, frame) implies {
            &&& frame.size == self.arch().frame_size((path.len() - 1) as nat)
            &&& path.to_vaddr(self.arch()).aligned(frame.size.as_nat())
            &&& frame.base.aligned(frame.size.as_nat())
            &&& frame.base.0 >= self.pmem_lb().0
            &&& frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0
        } by {
            // Prove the reached frame satisfy the invariants
            self.root.lemma_visited_entries_satisfy_invariants(path);
            assert(PTTreeNode::is_entry_valid(
                NodeEntry::Frame(frame),
                (path.len() - 1) as nat,
                self.root.config,
            ));
            assert(self.arch().is_valid_frame_size(frame.size));

            // Prove alignment
            assert(frame.base.aligned(frame.size.as_nat()));
            assert(frame.base.0 >= self.pmem_lb().0);
            assert(frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0);
            path.lemma_to_vaddr_frame_alignment(self.arch());
        }
    }

    /// Lemma. All `(vbase, frame)` mappings have valid size and alignment.
    pub proof fn lemma_mappings_valid(self)
        requires
            self.invariants(),
        ensures
            forall|vbase, frame| #[trigger]
                self.mappings().contains_pair(vbase, frame) ==> {
                    &&& self.arch().is_valid_frame_size(frame.size)
                    &&& vbase.aligned(frame.size.as_nat())
                    &&& frame.base.aligned(frame.size.as_nat())
                    &&& frame.base.0 >= self.pmem_lb().0
                    &&& frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0
                },
    {
        assert forall|vbase, frame| #[trigger] self.mappings().contains_pair(vbase, frame) implies {
            &&& self.arch().is_valid_frame_size(frame.size)
            &&& vbase.aligned(frame.size.as_nat())
            &&& frame.base.aligned(frame.size.as_nat())
            &&& frame.base.0 >= self.pmem_lb().0
            &&& frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0
        } by {
            let path = choose|path: PTTreePath|
                #![auto]
                {
                    &&& path.valid(self.arch(), 0)
                    &&& self.root.recursive_visit(path).len() == path.len()
                    &&& self.root.recursive_visit(path).last() == NodeEntry::Frame(frame)
                    &&& path.to_vaddr(self.arch()) == vbase
                };
            assert(self.path_mappings().contains_pair(path, frame));
            self.lemma_path_mappings_valid();
        }
    }

    /// Lemma. Path mappings can not have 2 keys `a` and `b` such that `a` is prefix of `b`.
    pub proof fn lemma_path_mappings_no_prefix(self)
        requires
            self.invariants(),
        ensures
            forall|path1, path2|
                self.path_mappings().contains_key(path1) && self.path_mappings().contains_key(path2)
                    ==> path1 == path2 || !path1.has_prefix(path2),
    {
        assert forall|path1, path2|
            self.path_mappings().contains_key(path1) && self.path_mappings().contains_key(
                path2,
            ) implies path1 == path2 || !path1.has_prefix(path2) by {
            if path1 != path2 {
                if path1.has_prefix(path2) {
                    // Proof by contradiction
                    let visited1 = self.root.recursive_visit(path1);
                    let visited2 = self.root.recursive_visit(path2);
                    assert(visited1.len() == path1.len());
                    assert(visited2.len() == path2.len());
                    // Prove `path2.len() - 1` and `path1.len() - 1` are different
                    if path1.len() == path2.len() {
                        path1.lemma_prefix_equals_full(path2);
                    }
                    assert(path2.len() < path1.len());
                    self.root.lemma_visit_preserves_prefix(path1, path2);
                    assert(visited1[path2.len() - 1] == visited2.last());
                    assert(visited2.last() is Frame);
                    assert(visited1.last() is Frame);
                    // `visited1` cannot have 2 frames (lemma), contradiction
                    self.root.lemma_visited_entry_is_node_except_final(path1);
                }
            }
        }
    }

    /// Lemma. All `(path, frame)` mappings do not overlap in virtual memory.
    pub proof fn lemma_path_mappings_nonoverlap_in_vmem(self)
        requires
            self.invariants(),
        ensures
            forall|path1, path2, frame1, frame2|
                self.path_mappings().contains_pair(path1, frame1)
                    && self.path_mappings().contains_pair(path2, frame2) ==> path1 == path2
                    || !VAddr::overlap(
                    path1.to_vaddr(self.arch()),
                    frame1.size.as_nat(),
                    path2.to_vaddr(self.arch()),
                    frame2.size.as_nat(),
                ),
    {
        assert forall|path1, path2, frame1, frame2|
            self.path_mappings().contains_pair(path1, frame1) && self.path_mappings().contains_pair(
                path2,
                frame2,
            ) implies path1 == path2 || !VAddr::overlap(
            path1.to_vaddr(self.arch()),
            frame1.size.as_nat(),
            path2.to_vaddr(self.arch()),
            frame2.size.as_nat(),
        ) by {
            if path1 != path2 {
                self.lemma_path_mappings_no_prefix();
                assert(!path1.has_prefix(path2));
                assert(!path2.has_prefix(path1));
                PTTreePath::lemma_first_diff_idx_exists(path1, path2);
                let first_diff_idx = PTTreePath::first_diff_idx(path1, path2);
                assert(path1.0[first_diff_idx] != path2.0[first_diff_idx]);

                self.lemma_path_mappings_valid();
                if path1.0[first_diff_idx] < path2.0[first_diff_idx] {
                    PTTreePath::lemma_path_order_implies_vaddr_order(self.arch(), path1, path2);
                    assert(path1.to_vaddr(self.arch()).0 + frame1.size.as_nat() <= path2.to_vaddr(
                        self.arch(),
                    ).0);
                } else {
                    PTTreePath::lemma_path_order_implies_vaddr_order(self.arch(), path2, path1);
                    assert(path2.to_vaddr(self.arch()).0 + frame2.size.as_nat() <= path1.to_vaddr(
                        self.arch(),
                    ).0);
                }
            }
        }
    }

    /// Lemma. All `(vbase, frame)` mappings do not overlap in virtual memory.
    pub proof fn lemma_mappings_nonoverlap_in_vmem(self)
        requires
            self.invariants(),
        ensures
            forall|vbase1, frame1, vbase2, frame2|
                self.mappings().contains_pair(vbase1, frame1) && self.mappings().contains_pair(
                    vbase2,
                    frame2,
                ) ==> vbase1 == vbase2 || !VAddr::overlap(
                    vbase1,
                    frame1.size.as_nat(),
                    vbase2,
                    frame2.size.as_nat(),
                ),
    {
        assert forall|vbase1, frame1, vbase2, frame2|
            self.mappings().contains_pair(vbase1, frame1) && self.mappings().contains_pair(
                vbase2,
                frame2,
            ) implies vbase1 == vbase2 || !VAddr::overlap(
            vbase1,
            frame1.size.as_nat(),
            vbase2,
            frame2.size.as_nat(),
        ) by {
            let (path1, path2) = choose|path1: PTTreePath, path2: PTTreePath|
                #![auto]
                {
                    &&& path1.valid(self.arch(), 0)
                    &&& path2.valid(self.arch(), 0)
                    &&& self.root.recursive_visit(path1).len() == path1.len()
                    &&& self.root.recursive_visit(path2).len() == path2.len()
                    &&& self.root.recursive_visit(path1).last() == NodeEntry::Frame(frame1)
                    &&& self.root.recursive_visit(path2).last() == NodeEntry::Frame(frame2)
                    &&& path1.to_vaddr(self.arch()) == vbase1
                    &&& path2.to_vaddr(self.arch()) == vbase2
                };
            assert(self.path_mappings().contains_pair(path1, frame1));
            assert(self.path_mappings().contains_pair(path2, frame2));
            self.lemma_path_mappings_nonoverlap_in_vmem();
        }
    }

    /// Lemma. A successful `map` operation adds the `(vbase, frame)` pair to mappings.
    pub proof fn lemma_map_adds_mapping(self, vbase: VAddr, frame: Frame)
        requires
            self.invariants(),
            self.arch().is_valid_frame_size(frame.size),
            vbase.aligned(frame.size.as_nat()),
            frame.base.aligned(frame.size.as_nat()),
            frame.base.0 >= self.pmem_lb().0,
            frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0,
        ensures
            self.map(vbase, frame) is Ok ==> self.map(vbase, frame).unwrap().mappings()
                === self.mappings().insert(vbase, frame),
    {
        let path = PTTreePath::from_vaddr(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        PTTreePath::lemma_from_vaddr_yields_valid_path(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        // Check if already mapped
        let visited = self.root.recursive_visit(path);
        if visited.last() is Empty {
            let new = Self::new(self.root.recursive_insert(path, frame));
            self.root.lemma_path_mappings_after_insertion_contains_new_mapping(path, frame);
            assert(new.path_mappings().contains_pair(path, frame));

            assert forall|path2: PTTreePath| new.path_mappings().contains_key(path2) implies path2
                == path || self.path_mappings().contains_key(path2) by {
                if path2 != path {
                    assert(self.root.recursive_visit(path2).last() == new.root.recursive_visit(
                        path2,
                    ).last());
                }
            }
            assert(new.path_mappings() === self.path_mappings().insert(path, frame));
            assert(new.mappings() === self.mappings().insert(vbase, frame));
        }
    }

    /// Lemma. A successful `unmap` operation removes the `(vbase, frame)` pair from mappings.
    pub proof fn lemma_unmap_removes_mapping(self, vbase: VAddr)
        requires
            self.invariants(),
        ensures
            self.unmap(vbase) is Ok ==> self.unmap(vbase).unwrap().mappings()
                === self.mappings().remove(vbase),
    {
        // TODO
        assume(false);
    }

    /// Lemma. `query` succeeds iff the address is within a mapped region.
    pub proof fn lemma_query_succeeds(self, vaddr: VAddr)
        requires
            self.invariants(),
        ensures
            self.query(vaddr) is Ok ==> {
                &&& exists|vbase, frame| #[trigger]
                    self.mappings().contains_pair(vbase, frame) && vaddr.within(
                        vbase,
                        frame.size.as_nat(),
                    )
                // &&& self.query(vaddr).unwrap() == choose|vbase: VAddr, frame: Frame| #[trigger]
                //     self.mappings().contains_pair(vbase, frame) && vaddr.within(
                //         vbase,
                //         frame.size.as_nat(),
                //     )

            },
    {
        let path = PTTreePath::from_vaddr(
            vaddr,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        let visited = self.root.recursive_visit(path);
        match visited.last() {
            NodeEntry::Frame(frame) => {
                let vbase = self.arch().vbase_of_va(vaddr, (visited.len() - 1) as nat);
                assert(self.mappings().contains_pair(vbase, frame));
                assume(vaddr.within(vbase, frame.size.as_nat()));
            },
            _ => (),
        }
    }

    /// Lemma. `query` fails iff there is no mapping for the address.
    pub proof fn lemma_query_fails(self, vaddr: VAddr)
        requires
            self.invariants(),
        ensures
            self.query(vaddr) is Err ==> {
                !exists|vbase, frame| #[trigger]
                    self.mappings().contains_pair(vbase, frame) && vaddr.within(
                        vbase,
                        frame.size.as_nat(),
                    )
            },
    {
        // TODO
        assume(false);
    }

    /// Theorem. `map` preserves invariants.
    pub proof fn map_preserves_invariants(self, vbase: VAddr, frame: Frame)
        requires
            self.invariants(),
            self.arch().is_valid_frame_size(frame.size),
            vbase.aligned(frame.size.as_nat()),
            frame.base.aligned(frame.size.as_nat()),
            frame.base.0 >= self.pmem_lb().0,
            frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0,
        ensures
            self.map(vbase, frame) is Ok ==> self.map(vbase, frame).unwrap().invariants(),
    {
        let path = PTTreePath::from_vaddr(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        // Prove `path` is valid
        PTTreePath::lemma_from_vaddr_yields_valid_path(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        self.root.lemma_insert_preserves_invariants(path, frame);
    }

    /// Theorem. `unmap` preserves invariants.
    pub proof fn unmap_preserves_invariants(self, vbase: VAddr)
        requires
            self.invariants(),
        ensures
            self.unmap(vbase) is Ok ==> self.unmap(vbase).unwrap().invariants(),
    {
        // `path` is the path used to query `vbase`
        let path = PTTreePath::from_vaddr(
            vbase,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        PTTreePath::lemma_from_vaddr_yields_valid_path(
            vbase,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        let visited = self.root.recursive_visit(path);
        if let NodeEntry::Frame(frame) = visited.last() {
            // There is a mapping with base address `base`
            // The last visited entry satisfies invariants
            self.root.lemma_visited_entries_satisfy_invariants(path);
            assert(PTTreeNode::is_entry_valid(
                visited.last(),
                (visited.len() - 1) as nat,
                self.root.config,
            ));
            // Prove `self.arch().level_of_frame_size(frame.size)` will return a valid level
            self.root.lemma_visit_length_bounds(path);
            assert(visited.len() - 1 < self.arch().level_count());
            assert(self.arch().is_valid_frame_size(frame.size));

            // `path2` is the right path to the target entry
            let path2 = PTTreePath::from_vaddr(
                vbase,
                self.arch(),
                self.arch().level_of_frame_size(frame.size),
            );
            // Prove `path2` is valid
            PTTreePath::lemma_from_vaddr_yields_valid_path(
                vbase,
                self.arch(),
                self.arch().level_of_frame_size(frame.size),
            );
            self.root.lemma_remove_preserves_invariants(path2);
        }
    }

    /// Theorem. `map` refines `PageTableState::map`.
    pub proof fn map_refinement(self, vbase: VAddr, frame: Frame)
        requires
            self.invariants(),
            self@.map_pre(vbase, frame),
        ensures
            if let Ok(new) = self.map(vbase, frame) {
                PageTableState::map(self@, new@, vbase, frame, Ok(()))
            } else {
                PageTableState::map(self@, self@, vbase, frame, Err(()))
            },
    {
        let path = PTTreePath::from_vaddr(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        let visited = self.root.recursive_visit(path);
        if visited.last() is Empty {
            // TODO
            assume(!self@.overlaps_vmem(vbase, frame));
            self.lemma_map_adds_mapping(vbase, frame);
        } else {
            // TODO
            assume(self@.overlaps_vmem(vbase, frame));
        }
    }

    /// Theorem. `unmap` refines `PageTableState::unmap`.
    pub proof fn unmap_refinement(self, vbase: VAddr)
        requires
            self.invariants(),
            self@.unmap_pre(vbase),
        ensures
            if let Ok(new) = self.unmap(vbase) {
                PageTableState::unmap(self@, new@, vbase, Ok(()))
            } else {
                PageTableState::unmap(self@, self@, vbase, Err(()))
            },
    {
        if let Ok((_, frame)) = self.query(vbase) {
            self.lemma_query_succeeds(vbase);
            // TODO
            assume(self.mappings().contains_key(vbase));
            self.lemma_unmap_removes_mapping(vbase);
        } else {
            self.lemma_query_fails(vbase);
            if self.mappings().contains_key(vbase) {
                // Proof by contradiction
                assert(self.mappings().contains_pair(vbase, self.mappings()[vbase]));
                assert(vbase.within(vbase, self.mappings()[vbase].size.as_nat()));
            }
            assert(!self.mappings().contains_key(vbase));
        }
    }

    /// Theorem. `query` refines `PageTableState::query`.
    pub proof fn query_refinement(self, vaddr: VAddr)
        requires
            self.invariants(),
            self@.query_pre(vaddr),
        ensures
            PageTableState::query(self@, self@, vaddr, self.query(vaddr)),
    {
        match self.query(vaddr) {
            Ok(_) => self.lemma_query_succeeds(vaddr),
            Err(_) => self.lemma_query_fails(vaddr),
        }
    }
}

} // verus!
