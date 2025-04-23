//! Abstract page table tree model, provides refinement proof.
use vstd::prelude::*;

use super::{
    node::{NodeEntry, PTConfig, PTTreeNode},
    path::PTTreePath,
};
use crate::{
    imp::lemmas::lemma_map_eq_pair,
    spec::{
        addr::{PAddr, VAddr},
        arch::PTArch,
        frame::Frame,
        pt_spec::{PTConstants, PageTableState},
    },
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
            self.root.lemma_at_most_one_path_for_vbase_in_path_mappings(vbase);
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
        PTTreePath::lemma_to_vaddr_is_inverse_of_from_vaddr(self.arch(), vbase, path);
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
                new.root.lemma_at_most_one_path_for_vbase_in_path_mappings(vbase);
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
                let real_path = self.root.real_path(path);
                self.root.lemma_visit_length_bounds(path);
                self.root.lemma_real_path_visits_same_entry(path);
                assert(self.root.path_mappings().contains_pair(real_path, frame));
                let vbase = real_path.to_vaddr(self.arch());
                self.lemma_mappings_consistent_with_path_mappings();
                assert(self.mappings().contains_pair(vbase, frame));
                // TODO
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
