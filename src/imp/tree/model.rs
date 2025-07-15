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
    pub open spec fn invariants(self) -> bool {
        &&& self.root.level == 0
        &&& self.root.invariants()
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
    pub open spec fn map(self, vbase: VAddr, frame: Frame) -> PagingResult<Self>
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
        let (node, res) = self.root.recursive_insert(path, frame);
        if res is Ok {
            Ok(Self::new(node))
        } else {
            Err(())
        }
    }

    /// Unmap a virtual address.
    ///
    /// If unmapping succeeds, return `Ok` and the updated tree.
    pub open spec fn unmap(self, vbase: VAddr) -> PagingResult<Self>
        recommends
            self.invariants(),
    {
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        let (node, res) = self.root.recursive_remove(path);
        if res is Ok {
            Ok(Self::new(node))
        } else {
            Err(())
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
        let visited = self.root.recursive_visit(path);
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
                    &&& self.root.recursive_visit(path).len() == path.len()
                    &&& self.root.recursive_visit(path).last() == NodeEntry::Frame(frame)
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
                    &&& self.root.recursive_visit(path1).len() == path1.len()
                    &&& self.root.recursive_visit(path2).len() == path2.len()
                    &&& self.root.recursive_visit(path1).last() == NodeEntry::Frame(frame1)
                    &&& self.root.recursive_visit(path2).last() == NodeEntry::Frame(frame2)
                    &&& path1.to_vaddr(self.arch()) == vbase1
                    &&& path2.to_vaddr(self.arch()) == vbase2
                };
            assert(self.root.path_mappings().contains_pair(path1, frame1));
            assert(self.root.path_mappings().contains_pair(path2, frame2));
            self.root.lemma_path_mappings_nonoverlap_in_vmem();
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
            self.map(vbase, frame) is Ok,
        ensures
            self.map(vbase, frame).unwrap().mappings() === self.mappings().insert(vbase, frame),
    {
        let new = self.map(vbase, frame).unwrap();
        self.map_preserves_invariants(vbase, frame);

        // `path` is the path to the entry containing the mapping.
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        PTTreePath::lemma_from_vaddr_root_yields_valid_path(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        PTTreePath::lemma_to_vaddr_is_inverse_of_from_vaddr_root(self.arch(), vbase, path);
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
                assert(exists|path2: PTTreePath| #[trigger]
                    new.root.path_mappings().contains_key(path2) && vbase2 == path2.to_vaddr(
                        self.arch(),
                    ) && new.root.path_mappings().index(path2) == frame2);
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
                assert(exists|path2: PTTreePath| #[trigger]
                    self.root.path_mappings().contains_key(path2) && vbase2 == path2.to_vaddr(
                        self.arch(),
                    ) && self.root.path_mappings().index(path2) == frame2);
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

    /// Lemma. A successful `unmap` operation removes the `(vbase, frame)` pair from mappings.
    pub proof fn lemma_unmap_removes_mapping(self, vbase: VAddr)
        requires
            self.invariants(),
            self.unmap(vbase) is Ok,
        ensures
            self.unmap(vbase).unwrap().mappings() === self.mappings().remove(vbase),
    {
        let new = self.unmap(vbase).unwrap();
        self.unmap_preserves_invariants(vbase);
        self.lemma_query_succeeds(vbase);
        // TODO
        assume(false);
    }

    /// Lemma. `query` succeeds if the address is within a mapped region.
    pub proof fn lemma_query_succeeds(self, vaddr: VAddr)
        requires
            self.invariants(),
            self.query(vaddr) is Ok,
        ensures
            exists|vbase, frame| #[trigger]
                self.mappings().contains_pair(vbase, frame) && vaddr.within(
                    vbase,
                    frame.size.as_nat(),
                ),
            self.query(vaddr).unwrap() == choose|vbase: VAddr, frame: Frame| #[trigger]
                self.mappings().contains_pair(vbase, frame) && vaddr.within(
                    vbase,
                    frame.size.as_nat(),
                ),
    {
        let path = PTTreePath::from_vaddr_root(
            vaddr,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        let visited = self.root.recursive_visit(path);
        // `query` succeeds implies `visited.last()` is a frame.
        assert(visited.last() is Frame);
        let frame = visited.last()->Frame_0;

        let real_path = self.root.real_path(path);
        self.root.lemma_visit_length_bounds(path);
        self.root.lemma_real_path_visits_same_entry(path);
        assert(self.root.path_mappings().contains_pair(real_path, frame));
        let vbase = real_path.to_vaddr(self.arch());
        self.lemma_mappings_consistent_with_path_mappings();
        assert(self.mappings().contains_pair(vbase, frame));
        // TODO
        assume(real_path.to_vaddr(self.arch()) == self.arch().vbase(
            vaddr,
            (real_path.len() - 1) as nat,
        ));
        assume(vaddr.within(vbase, frame.size.as_nat()));

        // Prove there is only one mapped region that contains `vaddr`.
        assert forall|vbase2, frame2| #[trigger]
            self.mappings().contains_pair(vbase2, frame2) && vaddr.within(
                vbase2,
                frame2.size.as_nat(),
            ) implies vbase2 == vbase by {
            assert(VAddr::overlap(vbase, frame.size.as_nat(), vbase2, frame2.size.as_nat()));
            self.lemma_mappings_nonoverlap_in_vmem();
        }
    }

    /// Lemma. `query` fails if there is no mapping for the address.
    pub proof fn lemma_query_fails(self, vaddr: VAddr)
        requires
            self.invariants(),
            self.query(vaddr) is Err,
        ensures
            !exists|vbase, frame| #[trigger]
                self.mappings().contains_pair(vbase, frame) && vaddr.within(
                    vbase,
                    frame.size.as_nat(),
                ),
    {
        if exists|vbase, frame| #[trigger]
            self.mappings().contains_pair(vbase, frame) && vaddr.within(
                vbase,
                frame.size.as_nat(),
            ) {
            // Proof by contradiction
            let (vbase, frame) = choose|vbase: VAddr, frame: Frame| #[trigger]
                self.mappings().contains_pair(vbase, frame) && vaddr.within(
                    vbase,
                    frame.size.as_nat(),
                );
            let path = PTTreePath::from_vaddr_root(
                vaddr,
                self.arch(),
                (self.arch().level_count() - 1) as nat,
            );
            let base_path = choose|base_path| #[trigger]
                self.root.path_mappings().contains_key(base_path) && base_path.to_vaddr(self.arch())
                    == vbase;
            // TODO
            assume(path.has_prefix(base_path));

            // Visit sequence of `base_path` is a prefix of `path`
            self.root.lemma_visit_preserves_prefix(path, base_path);
            assert(self.root.recursive_visit(base_path).last() is Frame);
            // Frame can only presents at the last entry of the visit sequence
            self.root.lemma_visited_entry_is_node_except_final(path);
            assert(self.root.recursive_visit(path) == self.root.recursive_visit(base_path));
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
            self.map(vbase, frame) is Ok,
        ensures
            self.map(vbase, frame).unwrap().invariants(),
    {
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        // Prove `path` is valid
        PTTreePath::lemma_from_vaddr_root_yields_valid_path(
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
            self.unmap(vbase) is Ok,
        ensures
            self.unmap(vbase).unwrap().invariants(),
    {
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        PTTreePath::lemma_from_vaddr_root_yields_valid_path(
            vbase,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        self.root.lemma_real_path_valid(path);
        self.root.lemma_remove_preserves_invariants(self.root.real_path(path));
    }

    /// Theorem. `map` refines `PageTableState::map`.
    pub proof fn map_refinement(self, vbase: VAddr, frame: Frame)
        requires
            self.invariants(),
            self@.map_pre(vbase, frame),
        ensures
            match self.map(vbase, frame) {
                Ok(new) => PageTableState::map(self@, new@, vbase, frame, Ok(())),
                Err(_) => PageTableState::map(self@, self@, vbase, frame, Err(())),
            },
    {
        let path = PTTreePath::from_vaddr_root(
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
            match self.unmap(vbase) {
                Ok(new) => PageTableState::unmap(self@, new@, vbase, Ok(())),
                Err(_) => PageTableState::unmap(self@, self@, vbase, Err(())),
            },
    {
        let path = PTTreePath::from_vaddr_root(
            vbase,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        let visited = self.root.recursive_visit(path);
        self.root.lemma_visited_entries_satisfy_invariants(path);
        if let NodeEntry::Frame(frame) = visited.last() {
            if vbase.aligned(frame.size.as_nat()) {
                // TODO
                assume(self.mappings().contains_key(vbase));
                self.lemma_unmap_removes_mapping(vbase);
            } else {
                assert(self.query(vbase) is Ok);
                self.lemma_query_succeeds(vbase);
                let (vbase2, frame2) = self.query(vbase).unwrap();
                if self.mappings().contains_key(vbase) {
                    if vbase2 != vbase {
                        self.lemma_mappings_nonoverlap_in_vmem();
                        assert(VAddr::overlap(
                            vbase,
                            self.mappings()[vbase].size.as_nat(),
                            vbase2,
                            frame2.size.as_nat(),
                        ));
                        assert(false);
                    } else {
                        assert(frame2 == frame);
                        self.lemma_mappings_valid();
                        assert(vbase.aligned(frame.size.as_nat()));
                        assert(false);
                    }
                }
            }
        } else {
            // TODO
            assume(!self.mappings().contains_key(vbase));
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
        // TODO
        assume(false);
    }
}

} // verus!
