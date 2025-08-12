//! Abstract page table tree model, provides refinement proof.
use vstd::prelude::*;

use super::{
    node::{NodeEntry, PTTreeNode},
    path::PTTreePath,
};
use crate::{
    common::{
        addr::{PAddr, VAddr},
        arch::PTArch,
        frame::Frame,
        PagingResult,
    },
    imp::lemmas::lemma_map_eq_pair,
    spec::page_table::{PTConstants, PageTableState},
};

verus! {

// Use path related lemmas.
broadcast use super::path::group_pt_tree_path_lemmas;

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
    pub open spec fn empty(config: PTConstants) -> Self {
        Self::new(PTTreeNode::new(config, 0))
    }

    /// Invariants. The tree structure and node configurations are valid.
    /// The tree is fully populated or empty.
    pub open spec fn invariants(self) -> bool {
        &&& self.root.level == 0
        &&& self.root.invariants()
        &&& self.root.fully_populated() || self.root.empty()
    }

    /// Get page table architecture.
    pub open spec fn arch(self) -> PTArch {
        self.root.constants.arch
    }

    /// Get physical memory lower bound.
    pub open spec fn pmem_lb(self) -> PAddr {
        self.root.constants.pmem_lb
    }

    /// Get physical memory upper bound.
    pub open spec fn pmem_ub(self) -> PAddr {
        self.root.constants.pmem_ub
    }

    /// Interpret the tree as `(vbase, frame)` mappings.
    pub open spec fn mappings(self) -> Map<VAddr, Frame> {
        Map::new(
            |vbase: VAddr|
                exists|path| #[trigger]
                    self.root.path_mappings().contains_key(path) && path.to_vaddr(self.arch())
                        == vbase,
            |vbase: VAddr|
                {
                    let path = choose|path| #[trigger]
                        self.root.path_mappings().contains_key(path) && path.to_vaddr(self.arch())
                            == vbase;
                    self.root.path_mappings().index(path)
                },
        )
    }

    /// If there exists a mapping for `vaddr`.
    pub open spec fn has_mapping_for(self, vaddr: VAddr) -> bool {
        exists|vbase: VAddr, frame: Frame|
            {
                &&& #[trigger] self.mappings().contains_pair(vbase, frame)
                &&& vaddr.within(vbase, frame.size.as_nat())
            }
    }

    /// Get the mapping for `vaddr`.
    pub open spec fn mapping_for(self, vaddr: VAddr) -> (VAddr, Frame)
        recommends
            self.has_mapping_for(vaddr),
    {
        choose|vbase: VAddr, frame: Frame|
            {
                &&& #[trigger] self.mappings().contains_pair(vbase, frame)
                &&& vaddr.within(vbase, frame.size.as_nat())
            }
    }

    /// If mapping `(vaddr, frame)` overlaps with existing virtual memory.
    pub open spec fn overlaps_vmem(self, vbase: VAddr, frame: Frame) -> bool {
        exists|vbase2: VAddr|
            {
                &&& #[trigger] self.mappings().contains_key(vbase2)
                &&& VAddr::overlap(
                    vbase2,
                    self.mappings()[vbase2].size.as_nat(),
                    vbase,
                    frame.size.as_nat(),
                )
            }
    }

    /// View the tree as `PageTableState`.
    pub open spec fn view(self) -> PageTableState {
        PageTableState {
            mappings: self.mappings(),
            constants: PTConstants {
                arch: self.arch(),
                pmem_lb: self.pmem_lb(),
                pmem_ub: self.pmem_ub(),
            },
        }
    }

    /// Map a virtual address to a physical frame.
    ///
    /// If mapping succeeds, return `Ok` and the updated tree.
    pub open spec fn map(self, vbase: VAddr, frame: Frame) -> (Self, PagingResult)
        recommends
            self.invariants(),
            self.arch().is_valid_frame_size(frame.size),
            vbase.aligned(frame.size.as_nat()),
            frame.base.aligned(frame.size.as_nat()),
            frame.base.0 >= self.pmem_lb().0,
            frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0,
    {
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        let (node, res) = self.root.insert(path, frame);
        if res is Ok {
            (Self::new(node), Ok(()))
        } else {
            (self, Err(()))
        }
    }

    /// Unmap a virtual address.
    ///
    /// If unmapping succeeds, return `Ok` and the updated tree.
    pub open spec fn unmap(self, vbase: VAddr) -> (Self, PagingResult)
        recommends
            self.invariants(),
    {
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        let (node, res) = self.root.remove(path);
        if res is Ok {
            (Self::new(node.prune(path)), Ok(()))
        } else {
            (self, Err(()))
        }
    }

    /// Query a virtual address, return the mapped physical frame.
    ///
    /// If there is no mapping for the virtual address, return `Err(())`.
    pub open spec fn query(self, vaddr: VAddr) -> PagingResult<(VAddr, Frame)>
        recommends
            self.invariants(),
    {
        let path = PTTreePath::from_vaddr_root(
            vaddr,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        let visited = self.root.visit(path);
        match visited.last() {
            NodeEntry::Frame(frame) => Ok(
                (self.arch().vbase(vaddr, (visited.len() - 1) as nat), frame),
            ),
            _ => Err(()),
        }
    }

    /// Lemma. `mappings` is consistent with `root.path_mappings`.
    pub proof fn lemma_mappings_consistent_with_path_mappings(self)
        requires
            self.invariants(),
        ensures
            forall|path: PTTreePath, frame: Frame| #[trigger]
                self.root.path_mappings().contains_pair(path, frame)
                    ==> self.mappings().contains_pair(path.to_vaddr(self.arch()), frame),
    {
        assert forall|path: PTTreePath, frame: Frame| #[trigger]
            self.root.path_mappings().contains_pair(
                path,
                frame,
            ) implies self.mappings().contains_pair(path.to_vaddr(self.arch()), frame) by {
            let vbase = path.to_vaddr(self.arch());
            assert(self.mappings().contains_key(vbase));
            self.root.lemma_path_mappings_has_at_most_one_path_for_vbase(vbase);
            assert(path == choose|path| #[trigger]
                self.root.path_mappings().contains_key(path) && path.to_vaddr(self.arch())
                    == vbase);
            assert(self.root.path_mappings().contains_pair(path, frame));
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
                    &&& self.root.visit(path).len() == path.len()
                    &&& self.root.visit(path).last() == NodeEntry::Frame(frame)
                    &&& path.to_vaddr(self.arch()) == vbase
                };
            assert(self.root.path_mappings().contains_pair(path, frame));
            self.root.lemma_path_mappings_valid();
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
                    &&& self.root.visit(path1).len() == path1.len()
                    &&& self.root.visit(path2).len() == path2.len()
                    &&& self.root.visit(path1).last() == NodeEntry::Frame(frame1)
                    &&& self.root.visit(path2).last() == NodeEntry::Frame(frame2)
                    &&& path1.to_vaddr(self.arch()) == vbase1
                    &&& path2.to_vaddr(self.arch()) == vbase2
                };
            assert(self.root.path_mappings().contains_pair(path1, frame1));
            assert(self.root.path_mappings().contains_pair(path2, frame2));
            self.root.lemma_path_mappings_nonoverlap_in_vmem();
        }
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
            self.map(vbase, frame).0.invariants(),
    {
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        self.root.lemma_insert_preserves_invariants(path, frame);
        if self.map(vbase, frame).1 is Ok {
            self.root.lemma_insert_preserves_fully_populated(path, frame);
        }
    }

    /// Lemma. `map` succeeds if the address does not overlap with any existing mapped region.
    pub proof fn lemma_nonoverlap_implies_map_ok(self, vbase: VAddr, frame: Frame)
        requires
            self.invariants(),
            self.arch().is_valid_frame_size(frame.size),
            vbase.aligned(frame.size.as_nat()),
            frame.base.aligned(frame.size.as_nat()),
            frame.base.0 >= self.pmem_lb().0,
            frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0,
            !self.overlaps_vmem(vbase, frame),
        ensures
            self.map(vbase, frame).1 is Ok,
    {
        let (new, res) = self.map(vbase, frame);
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );

        if self.root.empty() {
            // Tree is empty, insertion succeeds trivially
            self.root.lemma_empty_implies_insert_ok(path, frame);
        } else {
            // Tree is fully populated
            assert(self.root.fully_populated());
            if res is Err {
                // Prove by contradiction
                self.root.lemma_insert_fails_implies_prefix(path, frame);
                let path2 = choose|path2: PTTreePath| #[trigger]
                    self.root.path_mappings().contains_key(path2) && (path2.has_prefix(path)
                        || path.has_prefix(path2));
                let frame2 = self.root.path_mappings()[path2];
                self.root.lemma_path_mappings_valid();

                assert(self.root.path_mappings().contains_pair(path2, frame2));
                self.lemma_mappings_consistent_with_path_mappings();
                assert(self.mappings().contains_pair(path2.to_vaddr(self.arch()), frame2));

                // The prefix relation implies that the two frames overlap
                if path.has_prefix(path2) {
                    PTTreePath::lemma_to_vaddr_lower_bound(self.arch(), path, path2);
                    PTTreePath::lemma_to_vaddr_upper_bound(self.arch(), path, path2);
                    assert(VAddr::overlap(
                        path.to_vaddr(self.arch()),
                        frame.size.as_nat(),
                        path2.to_vaddr(self.arch()),
                        frame2.size.as_nat(),
                    ));
                } else {
                    PTTreePath::lemma_to_vaddr_lower_bound(self.arch(), path2, path);
                    PTTreePath::lemma_to_vaddr_upper_bound(self.arch(), path2, path);
                    assert(VAddr::overlap(
                        path2.to_vaddr(self.arch()),
                        frame2.size.as_nat(),
                        path.to_vaddr(self.arch()),
                        frame.size.as_nat(),
                    ));
                }
            }
        }
    }

    /// Lemma. The address does not overlap with any existing mapped region if `map` succeeds.
    pub proof fn lemma_map_ok_implies_nonoverlap(self, vbase: VAddr, frame: Frame)
        requires
            self.invariants(),
            self.arch().is_valid_frame_size(frame.size),
            vbase.aligned(frame.size.as_nat()),
            frame.base.aligned(frame.size.as_nat()),
            frame.base.0 >= self.pmem_lb().0,
            frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0,
            self.map(vbase, frame).1 is Ok,
        ensures
            !self.overlaps_vmem(vbase, frame),
    {
        let (new, res) = self.map(vbase, frame);
        self.map_preserves_invariants(vbase, frame);

        self.lemma_map_adds_mapping(vbase, frame);
        assert(new.mappings() == self.mappings().insert(vbase, frame));

        // The newly added mapping is not in the original mappings
        self.lemma_map_ok_implies_vbase_nonexist(vbase, frame);
        assert(!self.mappings().contains_key(vbase));

        // `self` and `new` both have non-overlapping mappings
        new.lemma_mappings_nonoverlap_in_vmem();
        self.lemma_mappings_nonoverlap_in_vmem();
        // So the newly added mapping cannot overlap with any existing mapping
        assert(forall|vbase2, frame2| #[trigger]
            self.mappings().contains_pair(vbase2, frame2) ==> !VAddr::overlap(
                vbase2,
                frame2.size.as_nat(),
                vbase,
                frame.size.as_nat(),
            ));
        assert(!self.overlaps_vmem(vbase, frame));
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
            self.map(vbase, frame).1 is Ok,
        ensures
            self.map(vbase, frame).0.mappings() === self.mappings().insert(vbase, frame),
    {
        let new = self.map(vbase, frame).0;
        self.map_preserves_invariants(vbase, frame);

        // `path` is the path to the entry containing the mapping.
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        assert(path.to_vaddr(self.arch()) == vbase);

        // `path_mappings` is updated according to lemma.
        self.root.lemma_insert_adds_path_mapping(path, frame);

        // `new.mappings()` is a subset of `self.mappings().insert(vbase, frame)`.
        assert forall|vbase2, frame2| #[trigger]
            new.mappings().contains_pair(vbase2, frame2) implies self.mappings().insert(
            vbase,
            frame,
        ).contains_pair(vbase2, frame2) by {
            if vbase2 != vbase {
                let path2 = choose|path2: PTTreePath| #[trigger]
                    new.root.path_mappings().contains_key(path2) && vbase2 == path2.to_vaddr(
                        self.arch(),
                    ) && new.root.path_mappings().index(path2) == frame2;
                assert(new.root.path_mappings().contains_pair(path2, frame2));
                // `lemma_insert_adds_path_mapping` ensures this.
                assert(self.root.path_mappings().insert(path, frame).contains_pair(path2, frame2));
                assert(path2 != path);
                assert(self.root.path_mappings().contains_pair(path2, frame2));
                // `self.mappings()` contains the mapping consistently.
                self.lemma_mappings_consistent_with_path_mappings();
                assert(self.mappings().contains_pair(vbase2, frame2));
                assert(self.mappings().insert(vbase, frame).contains_pair(vbase2, frame2));
            } else {
                new.root.lemma_path_mappings_has_at_most_one_path_for_vbase(vbase);
                // Only exists one path for `vbase` in path mappings, so `frame2 == frame`
                assert(frame2 == frame);
            }
        }
        // `self.mappings().insert(vbase, frame)` is a subset of `new.mappings()`.
        assert forall|vbase2, frame2| #[trigger]
            self.mappings().insert(vbase, frame).contains_pair(
                vbase2,
                frame2,
            ) implies new.mappings().contains_pair(vbase2, frame2) by {
            if vbase2 != vbase {
                assert(self.mappings().contains_pair(vbase2, frame2));
                let path2 = choose|path2: PTTreePath| #[trigger]
                    self.root.path_mappings().contains_key(path2) && vbase2 == path2.to_vaddr(
                        self.arch(),
                    ) && self.root.path_mappings().index(path2) == frame2;
                assert(self.root.path_mappings().contains_pair(path2, frame2));
                // `new.root.path_mappings()` is a superset of `self.root.path_mappings()`.
                assert(new.root.path_mappings().contains_pair(path2, frame2));
                // `new.mappings()` contains the mapping consistently.
                new.lemma_mappings_consistent_with_path_mappings();
                assert(new.mappings().contains_pair(vbase2, frame2));
            } else {
                assert(frame2 == frame);
                // `lemma_insert_adds_path_mapping` ensures this.
                assert(new.root.path_mappings().contains_pair(path, frame));
                // `new.mappings()` contains the mapping consistently.
                new.lemma_mappings_consistent_with_path_mappings();
                assert(new.mappings().contains_pair(vbase2, frame2));
            }
        }
        lemma_map_eq_pair(new.mappings(), self.mappings().insert(vbase, frame));
    }

    /// Lemma. `map` succeeds implies `vbase` not in `mappings()`.
    pub proof fn lemma_map_ok_implies_vbase_nonexist(self, vbase: VAddr, frame: Frame)
        requires
            self.invariants(),
            self.arch().is_valid_frame_size(frame.size),
            vbase.aligned(frame.size.as_nat()),
            frame.base.aligned(frame.size.as_nat()),
            frame.base.0 >= self.pmem_lb().0,
            frame.base.0 + frame.size.as_nat() <= self.pmem_ub().0,
            self.map(vbase, frame).1 is Ok,
        ensures
            !self.mappings().contains_key(vbase),
    {
        let new = self.map(vbase, frame).0;
        self.map_preserves_invariants(vbase, frame);

        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        self.root.lemma_insert_ok_implies_visit_reaches_empty(path, frame);

        if self.mappings().contains_key(vbase) {
            let path2 = choose|path: PTTreePath| #[trigger]
                self.root.path_mappings().contains_key(path) && path.to_vaddr(self.arch()) == vbase;
            PTTreePath::lemma_vaddr_eq_implies_real_prefix(self.arch(), path, path2);
            assert(self.root.visit(path2).last() is Frame);

            // The prefix relation leads to a contradiction of the lasted visited entry.
            if path.has_prefix(path2) {
                self.root.lemma_visited_entry_is_node_except_final(path);
                self.root.lemma_visit_preserves_prefix(path, path2);
                assert(false);
            } else {
                self.root.lemma_visited_entry_is_node_except_final(path2);
                self.root.lemma_visit_preserves_prefix(path2, path);
                assert(false);
            }
        }
    }

    /// Theorem. `unmap` preserves invariants.
    pub proof fn unmap_preserves_invariants(self, vbase: VAddr)
        requires
            self.invariants(),
            self.unmap(vbase).1 is Ok,
        ensures
            self.unmap(vbase).0.invariants(),
    {
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        self.root.lemma_remove_preserves_invariants(path);
        self.root.remove(path).0.lemma_prune_preserves_invariants(path);

        if self.root.empty() {
            self.root.lemma_empty_implies_remove_fail(path);
        }
        assert(self.root.fully_populated());
        self.root.lemma_prune_after_remove_preserves_fully_populated(path);
    }

    /// Lemma. `unmap` succeeds implies `vbase` in `mappings()`.
    pub proof fn lemma_unmap_ok_implies_vbase_exist(self, vbase: VAddr)
        requires
            self.invariants(),
            self@.unmap_pre(vbase),
            self.unmap(vbase).1 is Ok,
        ensures
            self.mappings().contains_key(vbase),
    {
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        let real_path = self.root.real_path(path);

        // Prove `real_path` is a real prefix of `path`.
        self.root.lemma_remove_ok_implies_visit_reaches_frame(path);
        self.root.lemma_visit_length_bounds(path);
        self.root.lemma_real_path_valid(path);
        self.root.lemma_real_path_visits_same_entry(path);
        assert(self.root.path_mappings().contains_key(real_path));
        assert(path.has_real_prefix(real_path));

        PTTreePath::lemma_real_prefix_implies_vaddr_eq(self.arch(), path, real_path);
        assert(real_path.to_vaddr(self.arch()) == vbase);
        assert(self.mappings().contains_key(vbase));
    }

    /// Lemma. `vbase` in `mappings()` implies `unmap` succeeds.
    pub proof fn lemma_vbase_exist_implies_unmap_ok(self, vbase: VAddr)
        requires
            self.invariants(),
            self@.unmap_pre(vbase),
            self.mappings().contains_key(vbase),
        ensures
            self.unmap(vbase).1 is Ok,
    {
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        let path2 = choose|path: PTTreePath| #[trigger]
            self.root.path_mappings().contains_key(path) && path.to_vaddr(self.arch()) == vbase;

        PTTreePath::lemma_to_vaddr_inverts_from_vaddr(self.arch(), vbase, path);
        PTTreePath::lemma_vaddr_eq_implies_real_prefix(self.arch(), path, path2);
        assert(path.has_real_prefix(path2));
        self.root.lemma_remove_real_prefix_ok(path, path2);
    }

    /// Lemma. A successful `unmap` operation removes the `(vbase, frame)` pair from mappings.
    pub proof fn lemma_unmap_removes_mapping(self, vbase: VAddr)
        requires
            self.invariants(),
            self@.unmap_pre(vbase),
            self.unmap(vbase).1 is Ok,
        ensures
            self.unmap(vbase).0.mappings() === self.mappings().remove(vbase),
    {
        let new = self.unmap(vbase).0;
        self.unmap_preserves_invariants(vbase);

        // `path` is the path to the entry containing the mapping.
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        let real_path = self.root.real_path(path);

        self.root.lemma_remove_ok_implies_visit_reaches_frame(path);
        self.root.lemma_visit_length_bounds(path);
        self.root.lemma_real_path_valid(path);
        self.root.lemma_real_path_visits_same_entry(path);
        assert(self.root.path_mappings().contains_key(real_path));
        assert(path.has_real_prefix(real_path));

        // `path_mappings` is updated according to lemma.
        self.root.lemma_remove_removes_path_mapping(path);
        self.root.lemma_remove_preserves_invariants(path);
        self.root.remove(path).0.lemma_prune_not_affect_path_mappings(path);

        // `new.mappings()` is a subset of `self.mappings().remove(vbase)`.
        assert forall|vbase2, frame2| #[trigger]
            new.mappings().contains_pair(vbase2, frame2) implies self.mappings().remove(
            vbase,
        ).contains_pair(vbase2, frame2) by {
            let path2 = choose|path2: PTTreePath| #[trigger]
                new.root.path_mappings().contains_key(path2) && vbase2 == path2.to_vaddr(
                    self.arch(),
                ) && new.root.path_mappings().index(path2) == frame2;
            assert(new.root.path_mappings().contains_pair(path2, frame2));
            // `lemma_remove_removes_path_mapping` ensures this.
            assert(self.root.path_mappings().remove(real_path).contains_pair(path2, frame2));
            assert(self.root.path_mappings().contains_pair(path2, frame2));

            // `self.mappings()` contains the mapping consistently.
            self.lemma_mappings_consistent_with_path_mappings();
            assert(self.mappings().contains_pair(vbase2, frame2));

            // Use prefix lemmas to show `vbase != vbase2`
            self.root.lemma_path_mappings_nonprefix();
            PTTreePath::lemma_nonprefix_implies_vaddr_inequality(self.arch(), path2, real_path);
            assert(path.to_vaddr(self.arch()) != vbase2);
            assert(self.mappings().remove(vbase).contains_pair(vbase2, frame2));
        }
        // `self.mappings().remove(vbase)` is a subset of `new.mappings()`.
        assert forall|vbase2, frame2| #[trigger]
            self.mappings().remove(vbase).contains_pair(
                vbase2,
                frame2,
            ) implies new.mappings().contains_pair(vbase2, frame2) by {
            assert(vbase2 != vbase);
            assert(self.mappings().contains_pair(vbase2, frame2));
            let path2 = choose|path2: PTTreePath| #[trigger]
                self.root.path_mappings().contains_key(path2) && vbase2 == path2.to_vaddr(
                    self.arch(),
                ) && self.root.path_mappings().index(path2) == frame2;
            assert(self.root.path_mappings().contains_pair(path2, frame2));
            // `new.root.path_mappings()` is a subset of `self.root.path_mappings()`.
            assert(new.root.path_mappings().contains_pair(path2, frame2));
            // `new.mappings()` contains the mapping consistently.
            new.lemma_mappings_consistent_with_path_mappings();
            assert(new.mappings().contains_pair(vbase2, frame2));
        }
        lemma_map_eq_pair(new.mappings(), self.mappings().remove(vbase));
    }

    /// Lemma. `query` succeeds if the address is within a mapped region.
    pub proof fn lemma_mapping_exist_implies_query_ok(self, vaddr: VAddr)
        requires
            self.invariants(),
            self.has_mapping_for(vaddr),
        ensures
            self.query(vaddr) is Ok,
            self.query(vaddr).unwrap() == self.mapping_for(vaddr),
    {
        let (vbase, frame) = self.mapping_for(vaddr);
        let path = choose|path: PTTreePath| #[trigger]
            self.root.path_mappings().contains_key(path) && path.to_vaddr(self.arch()) == vbase;
        assert(self.root.path_mappings().contains_pair(path, frame));

        // `path2` is the path used to find the mapping.
        let path2 = PTTreePath::from_vaddr_root(
            vaddr,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        self.root.lemma_path_mappings_valid();
        assert(vbase.0 <= vaddr.0 < vbase.0 + frame.size.as_nat());
        // Substitute address with path
        assert(path2.to_vaddr(self.arch()).0 <= vaddr.0 < path2.to_vaddr(self.arch()).0
            + self.arch().leaf_frame_size().as_nat());

        if !path2.has_prefix(path) {
            // Leads to a contradiction
            let diff_idx = PTTreePath::first_diff_idx(path, path2);
            if path.0[diff_idx] < path2.0[diff_idx] {
                PTTreePath::lemma_path_order_implies_vaddr_order(self.arch(), path, path2);
                assert(path.to_vaddr(self.arch()).0 + frame.size.as_nat() <= path2.to_vaddr(
                    self.arch(),
                ).0);
            } else {
                PTTreePath::lemma_path_order_implies_vaddr_order(self.arch(), path2, path);
                assert(path2.to_vaddr(self.arch()).0 + self.arch().leaf_frame_size().as_nat()
                    <= path.to_vaddr(self.arch()).0);
            }
            assert(false);
        }
        assert(path2.has_prefix(path));

        // Show that `path` is the real path of `path2`.
        self.root.lemma_visit_preserves_prefix(path2, path);
        self.root.lemma_visited_entry_is_node_except_final(path);
        self.root.lemma_visited_entry_is_node_except_final(path2);
        assert(self.root.visit(path) == self.root.visit(path2));
        path2.lemma_trim_prefix(path);
        assert(path2.trim(path.len()) == path);
        assert(self.root.real_path(path2) == path);

        let visited = self.root.visit(path2);
        assert(visited.last() == NodeEntry::Frame(frame));

        // TODO: add lemma to `PTTreePath`
        assume(self.arch().vbase(vaddr, (visited.len() - 1) as nat) == vbase);
    }

    /// Lemma. The address is within a mapped region if `query` succeeds.
    pub proof fn lemma_query_ok_implies_mapping_exist(self, vaddr: VAddr)
        requires
            self.invariants(),
            self.query(vaddr) is Ok,
        ensures
            self.has_mapping_for(vaddr),
    {
        let path = PTTreePath::from_vaddr_root(
            vaddr,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        let visited = self.root.visit(path);
        // `query` succeeds implies `visited.last()` is a frame
        assert(visited.last() is Frame);
        let frame = visited.last()->Frame_0;

        // Path mapping for `vaddr`
        let real_path = self.root.real_path(path);
        self.root.lemma_visit_length_bounds(path);
        self.root.lemma_real_path_visits_same_entry(path);
        assert(self.root.path_mappings().contains_pair(real_path, frame));

        // Mapping for `vaddr`
        let vbase = real_path.to_vaddr(self.arch());
        self.lemma_mappings_consistent_with_path_mappings();
        assert(self.mappings().contains_pair(vbase, frame));

        // TODO: add lemma to `PTTreePath`
        assume(vaddr.within(vbase, frame.size.as_nat()));

        // Prove there is only one mapped region that contains `vaddr`
        assert forall|vbase2, frame2| #[trigger]
            self.mappings().contains_pair(vbase2, frame2) && vaddr.within(
                vbase2,
                frame2.size.as_nat(),
            ) implies vbase2 == vbase by {
            // Prove by contradiction
            assert(VAddr::overlap(vbase, frame.size.as_nat(), vbase2, frame2.size.as_nat()));
            self.lemma_mappings_nonoverlap_in_vmem();
        }
    }

    /// Theorem. `map` refines `PageTableState::map`.
    pub proof fn map_refinement(self, vbase: VAddr, frame: Frame)
        requires
            self.invariants(),
            self@.map_pre(vbase, frame),
        ensures
            ({
                let (new, res) = self.map(vbase, frame);
                PageTableState::map(self@, new@, vbase, frame, res)
            }),
    {
        let (new, res) = self.map(vbase, frame);
        if !self.overlaps_vmem(vbase, frame) {
            self.lemma_nonoverlap_implies_map_ok(vbase, frame);
            self.lemma_map_adds_mapping(vbase, frame);
        } else {
            if res is Ok {
                // Prove by contradiction
                self.lemma_map_ok_implies_nonoverlap(vbase, frame);
            }
        }
    }

    /// Theorem. `unmap` refines `PageTableState::unmap`.
    pub proof fn unmap_refinement(self, vbase: VAddr)
        requires
            self.invariants(),
            self@.unmap_pre(vbase),
        ensures
            ({
                let (new, res) = self.unmap(vbase);
                PageTableState::unmap(self@, new@, vbase, res)
            }),
    {
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        if self.mappings().contains_key(vbase) {
            self.lemma_vbase_exist_implies_unmap_ok(vbase);
            self.lemma_unmap_removes_mapping(vbase);
        } else {
            if self.unmap(vbase).1 is Ok {
                // Prove by contradiction
                self.lemma_unmap_ok_implies_vbase_exist(vbase);
            }
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
        assert(self.mappings() == self@.mappings);  // I don't know why this is necessary

        let res = self.query(vaddr);
        if self.has_mapping_for(vaddr) {
            self.lemma_mapping_exist_implies_query_ok(vaddr);
        } else {
            if res is Ok {
                // Prove by contradiction
                self.lemma_query_ok_implies_mapping_exist(vaddr);
            }
        }
    }
}

} // verus!
