//! Tree model of the page table.
use vstd::prelude::*;

use crate::spec::{addr::VAddr, arch::PTArch, frame::Frame};

verus! {

/// Represents a path from a node to an entry in the page table tree.
///
/// The path is represented as a sequence of indices, where each index corresponds to
/// an entry in the page table node at a particular level of the hierarchy.
pub struct PTTreePath(pub Seq<nat>);

impl PTTreePath {
    /// Path length.
    pub open spec fn len(self) -> nat {
        self.0.len()
    }

    /// Pop head and return the remaining path.
    pub open spec fn step(self) -> (nat, PTTreePath)
        recommends
            self.len() > 0,
    {
        (self.0[0], PTTreePath(self.0.skip(1)))
    }

    /// Check if path is valid.
    pub open spec fn valid(self, arch: PTArch, start_level: nat) -> bool {
        &&& self.len() + start_level <= arch.level_count()
        &&& forall|i: int|
            0 <= i < self.len() ==> self.0[i] < arch.entry_count(i as nat + start_level)
    }

    /// Get a `PTPath` from a virtual address, used to query the page table.
    ///
    /// The last query level of the returned path is `level`, and the path has length `level + 1`.
    pub open spec fn from_vaddr(vaddr: VAddr, arch: PTArch, level: nat) -> PTTreePath
        recommends
            level < arch.level_count(),
    {
        PTTreePath(Seq::new(level + 1, |i: int| arch.pte_index_of_va(vaddr, i as nat)))
    }

    /// Lemma. `from_vaddr` returns a valid path.
    pub proof fn lemma_from_vaddr_valid(vaddr: VAddr, arch: PTArch, level: nat)
        requires
            level < arch.level_count(),
            arch.invariants(),
        ensures
            PTTreePath::from_vaddr(vaddr, arch, level).valid(arch, 0),
    {
        let path = PTTreePath::from_vaddr(vaddr, arch, level);
        assert forall|i: int| 0 <= i < path.len() implies path.0[i] < arch.entry_count(
            i as nat,
        ) by {
            // TODO: Verus cannot imply (a % b) < b with
            // See: https://verus-lang.github.io/verus/guide/nonlinear.html
            assume(arch.pte_index_of_va(vaddr, i as nat) < arch.entry_count(i as nat))
        }
    }
}

/// Represents a node in the page table tree, which can be either an intermediate node
/// or a leaf node mapping to a physical frame.
pub tracked struct PTTreeNode {
    /// The architecture of the page table.
    pub arch: PTArch,
    /// The level of the node in the page table hierarchy.
    pub level: nat,
    /// The entries of the node, which can be either sub-nodes, frames, or empty entries.
    pub entries: Seq<NodeEntry>,
}

/// Represents an entry in the page table node, which can be a sub-node, a physical frame,
/// or an empty entry.
pub tracked enum NodeEntry {
    /// A sub-node in the page table, representing an intermediate level of the page table hierarchy.
    Node(PTTreeNode),
    /// A physical frame mapped by the node, representing a leaf node in the page table tree.
    Frame(Frame),
    /// An empty entry in the page table, indicating that the corresponding virtual address range
    /// is not currently mapped or allocated.
    Empty,
}

impl PTTreeNode {
    /// If the node is a leaf node
    pub open spec fn is_leaf(self) -> bool {
        self.level == self.arch.level_count() - 1
    }

    /// Invariants of an entry in the node at the specified level.
    pub open spec fn inv_entry(self, entry: NodeEntry, level: nat) -> bool {
        match entry {
            NodeEntry::Node(node) => if level < self.arch.level_count() - 1 {
                node.level == level + 1 && node.arch == self.arch
            } else {
                false
            },
            NodeEntry::Frame(frame) => {
                &&& frame.size == self.arch.frame_size(level)
                &&& frame.base.aligned(frame.size.as_nat())
            },
            NodeEntry::Empty => true,
        }
    }

    /// Invariants. Recursively checks the invariants of the node and its sub-nodes.
    pub open spec fn invariants(self) -> bool
        decreases self.arch.level_count() - self.level,
    {
        &&& self.arch.invariants()
        &&& self.level < self.arch.level_count()
        &&& self.entries.len() == self.arch.entry_count(self.level)
        &&& forall|entry: NodeEntry| #[trigger]
            self.entries.contains(entry) ==> {
                &&& self.inv_entry(entry, self.level)
                &&& entry is Node ==> entry->Node_0.invariants()
            }
    }

    /// Creates an empty node.
    pub open spec fn new(arch: PTArch, level: nat) -> Self
        recommends
            level < arch.level_count(),
            arch.invariants(),
    {
        Self { arch, level, entries: seq![NodeEntry::Empty; arch.entry_count(level)] }
    }

    /// Creates an empty root node.
    pub open spec fn new_root(arch: PTArch) -> Self
        recommends
            arch.invariants(),
    {
        Self::new(arch, 0)
    }

    /// Lemma. `new` function implies invariants.
    pub proof fn lemma_new_implies_invariants(base: VAddr, level: nat, arch: PTArch)
        requires
            level < arch.level_count(),
            arch.invariants(),
        ensures
            Self::new(arch, level).invariants(),
    {
    }

    /// Update an entry in the node at the specified index.
    pub open spec fn update(self, index: nat, entry: NodeEntry) -> Self
        recommends
            index < self.entries.len(),
            self.inv_entry(entry, self.level),
    {
        Self { entries: self.entries.update(index as int, entry), ..self }
    }

    /// Visit the tree along `path` and return the sequence of entries visited.
    ///
    /// If a reached entry is `Empty` and `path` is not empty, then the visit
    /// terminates early and returns the sequence of entries visited so far.
    pub open spec fn recursive_visit(self, path: PTTreePath) -> Seq<NodeEntry>
        recommends
            self.invariants(),
            path.valid(self.arch, self.level),
        decreases path.len(),
    {
        if path.len() == 0 {
            seq![]
        } else {
            let (idx, remain) = path.step();
            let entry = self.entries[idx as int];
            match entry {
                NodeEntry::Node(node) => seq![entry].add(node.recursive_visit(remain)),
                _ => seq![entry],
            }
        }
    }

    /// Recursively insert a node or a frame at `path`.
    ///
    /// Intermmediate nodes are created if necessary. New entry will be inserted only if
    /// the entry at `path` is `Empty`, otherwise the tree will not be modified.
    pub open spec fn recursive_insert(self, path: PTTreePath, entry: NodeEntry) -> Self
        recommends
            self.invariants(),
            path.len() > 0,
            path.valid(self.arch, self.level),
            entry is Node || entry is Frame,
            self.inv_entry(entry, (self.level + path.len() - 1) as nat),
            entry is Node ==> entry->Node_0.invariants(),
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry2 = self.entries[idx as int];
        if path.len() <= 1 {
            match entry2 {
                NodeEntry::Empty => self.update(idx, entry),
                _ => self,
            }
        } else {
            match entry2 {
                NodeEntry::Node(node) => self.update(
                    idx,
                    NodeEntry::Node(node.recursive_insert(remain, entry)),
                ),
                NodeEntry::Empty => self.update(
                    idx,
                    NodeEntry::Node(
                        PTTreeNode::new(self.arch, self.level + 1).recursive_insert(remain, entry),
                    ),
                ),
                _ => self,
            }
        }
    }

    /// Recursively remove the entry at `path`.
    ///
    /// If the entry at `path` is already `Empty`, then the tree will not be modified.
    pub open spec fn recursive_remove(self, path: PTTreePath) -> Self
        recommends
            self.invariants(),
            path.len() > 0,
            path.valid(self.arch, self.level),
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        if path.len() <= 1 {
            self.update(idx, NodeEntry::Empty)
        } else {
            match entry {
                NodeEntry::Node(node) => self.update(
                    idx,
                    NodeEntry::Node(node.recursive_remove(remain)),
                ),
                _ => self,
            }
        }
    }

    /// Lemma. Entry sequence returned by `recursive_visit` has max length of `path.len()`.
    proof fn lemma_recursive_visit_max_length(self, path: PTTreePath)
        requires
            self.invariants(),
            path.valid(self.arch, self.level),
        ensures
            self.recursive_visit(path).len() <= path.len(),
        decreases path.len(),
    {
        if path.len() == 0 {
            assert(self.recursive_visit(path).len() == 0);
        } else {
            let (idx, remain) = path.step();
            let entry = self.entries[idx as int];
            assert(self.entries.contains(entry));
            match entry {
                NodeEntry::Node(node) => {
                    node.lemma_recursive_visit_max_length(remain);
                },
                _ => assert(self.recursive_visit(path).len() == 1),
            }
        }
    }

    /// Lemma. Each node visited by `recursive_visit` satisfies the invariants.
    proof fn lemma_visited_nodes_satisfy_invariants(self, path: PTTreePath)
        requires
            self.invariants(),
            path.valid(self.arch, self.level),
        ensures
            forall|entry: NodeEntry| #[trigger]
                self.recursive_visit(path).contains(entry) ==> (entry is Node
                    ==> entry->Node_0.invariants()),
        decreases path.len(),
    {
        if path.len() == 0 {
            assert(self.recursive_visit(path) === seq![]);
        } else {
            let (idx, remain) = path.step();
            let entry = self.entries[idx as int];
            assert(self.entries.contains(entry));
            assert(self.inv_entry(entry, self.level));
            match entry {
                NodeEntry::Node(node) => {
                    assert(self.recursive_visit(path) === seq![entry].add(
                        node.recursive_visit(remain),
                    ));
                    // Recursively prove `node.recursive_visit(remain)`
                    node.lemma_visited_nodes_satisfy_invariants(remain);
                    assert forall|entry2: NodeEntry| #[trigger]
                        self.recursive_visit(path).contains(entry2) implies !(entry2 is Node)
                        || entry2->Node_0.invariants() by {
                        if entry2 != entry {
                            // Satisfied because of recursive proof
                            assert(node.recursive_visit(remain).contains(entry2));
                        }
                    }
                },
                _ => (),
            }
        }
    }

    /// Lemma. Each entry visited by `visit` satisfies the invariants.
    pub proof fn lemma_visited_entries_satisfy_invariants(self, path: PTTreePath)
        requires
            self.invariants(),
            path.valid(self.arch, self.level),
        ensures
            forall|i: int|
                #![auto]
                0 <= i < self.recursive_visit(path).len() ==> self.inv_entry(
                    self.recursive_visit(path)[i],
                    self.level + i as nat,
                ),
        decreases path.len(),
    {
        if path.len() == 0 {
            assert(self.recursive_visit(path) === seq![]);
        } else {
            let (idx, remain) = path.step();
            let entry = self.entries[idx as int];
            assert(self.entries.contains(entry));
            assert(self.inv_entry(entry, self.level));
            match entry {
                NodeEntry::Node(node) => {
                    assert(self.recursive_visit(path) === seq![entry].add(
                        node.recursive_visit(remain),
                    ));
                    assert(node.level == self.level + 1);
                    // Recursively prove `node.recursive_visit(remain)` satisfies the invariants
                    node.lemma_visited_entries_satisfy_invariants(remain);
                },
                _ => (),
            }
        }
    }

    /// Lemma. If the path length equals the height (i.e. level_count - level) of the node,
    /// then the last entry visited is a frame or empty.
    proof fn lemma_last_visited_entry_is_frame_or_empty(self, path: PTTreePath)
        requires
            self.invariants(),
            path.valid(self.arch, self.level),
            self.arch.level_count() - self.level == path.len(),
        ensures
            self.recursive_visit(path).last() is Frame || self.recursive_visit(
                path,
            ).last() is Empty,
        decreases path.len(),
    {
        let visited = self.recursive_visit(path);
        if path.len() == 1 {
            // `self` is leaf, so the last entry is a frame or empty
            assert(self.is_leaf());
            let (idx, remain) = path.step();
            let entry = self.entries[idx as int];
            match entry {
                NodeEntry::Frame(_) => (),
                NodeEntry::Empty => (),
                _ => assume(false),
            }
            assert(visited === seq![entry]);
        } else {
            // `self` is not leaf, recursively prove `self.recursive_visit(remain)`
            assert(!self.is_leaf());
            let (idx, remain) = path.step();
            let entry = self.entries[idx as int];
            match entry {
                NodeEntry::Node(node) => {
                    assert(self.entries.contains(entry));
                    assert(self.inv_entry(entry, self.level));
                    assert(node.invariants());
                    // Recursively prove `node.recursive_visit(remain)`
                    node.lemma_last_visited_entry_is_frame_or_empty(remain)
                },
                _ => (),
            }
        }
    }

    /// Lemma. `update` function preserves invariants.
    pub proof fn lemma_update_preserves_invariants(self, index: nat, entry: NodeEntry)
        requires
            self.invariants(),
            0 <= index < self.entries.len(),
            self.inv_entry(entry, self.level),
            entry is Node ==> entry->Node_0.invariants(),
        ensures
            self.update(index, entry).invariants(),
    {
        let new = self.update(index, entry);
        assert forall|entry2: NodeEntry| #[trigger]
            new.entries.contains(entry2) implies self.inv_entry(entry2, self.level) by {
            if entry2 != entry {
                assert(self.entries.contains(entry2));
            }
        }
        assert forall|entry2: NodeEntry| #[trigger]
            new.entries.contains(entry2) implies match entry2 {
            NodeEntry::Node(node) => node.invariants(),
            _ => true,
        } by {
            if entry2 != entry {
                assert(self.entries.contains(entry2));
            }
        }
    }

    /// Lemma. `recursive_insert` function preserves invariants.
    pub proof fn lemma_recursive_insert_preserves_invariants(
        self,
        path: PTTreePath,
        entry: NodeEntry,
    )
        requires
            self.invariants(),
            path.len() > 0,
            path.valid(self.arch, self.level),
            entry is Node || entry is Frame,
            self.inv_entry(entry, (self.level + path.len() - 1) as nat),
            entry is Node ==> entry->Node_0.invariants(),
        ensures
            self.recursive_insert(path, entry).invariants(),
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry2 = self.entries[idx as int];
        if path.len() <= 1 {
            // Base case, proved by lemma
            self.lemma_update_preserves_invariants(idx, entry);
        } else {
            match entry2 {
                NodeEntry::Node(node) => {
                    assert(self.entries.contains(entry2));
                    assert(self.inv_entry(entry2, self.level));
                    assert(node.invariants());
                    // Recursively prove `node.recursive_insert(remain)`
                    node.lemma_recursive_insert_preserves_invariants(remain, entry);
                    // `node.recursive_update(remain, entry)` satisfies invariants,
                    // so the updated `self` also satisfy invariants by lemma
                    self.lemma_update_preserves_invariants(
                        idx,
                        NodeEntry::Node(node.recursive_insert(remain, entry)),
                    );
                },
                NodeEntry::Empty => {
                    let new = PTTreeNode::new(self.arch, self.level + 1);
                    // `new` satisfies invariants by construction
                    assert(new.invariants());
                    // Recursively prove `new.recursive_insert(remain)`
                    new.lemma_recursive_insert_preserves_invariants(remain, entry);
                    // `new.recursive_insert(remain, entry)` satisfies invariants,
                    // so the updated `self` also satisfy invariants by lemma
                    self.lemma_update_preserves_invariants(
                        idx,
                        NodeEntry::Node(new.recursive_insert(remain, entry)),
                    );
                },
                _ => (),
            }
        }
    }

    /// Lemma. `recursive_remove` function preserves invariants.
    pub proof fn lemma_recursive_remove_preserves_invariants(self, path: PTTreePath)
        requires
            self.invariants(),
            path.len() > 0,
            path.valid(self.arch, self.level),
        ensures
            self.recursive_remove(path).invariants(),
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry2 = self.entries[idx as int];
        if path.len() <= 1 {
            // Base case, proved by lemma
            self.lemma_update_preserves_invariants(idx, NodeEntry::Empty);
        } else {
            match entry2 {
                NodeEntry::Node(node) => {
                    assert(self.entries.contains(entry2));
                    assert(self.inv_entry(entry2, self.level));
                    assert(node.invariants());
                    // Recursively prove `node.recursive_remove(remain)`
                    node.lemma_recursive_remove_preserves_invariants(remain);
                    // `node.recursive_remove(remain)` satisfies invariants,
                    // so the updated `self` also satisfy invariants by lemma
                    self.lemma_update_preserves_invariants(
                        idx,
                        NodeEntry::Node(node.recursive_remove(remain)),
                    );
                },
                _ => (),
            }
        }
    }
}

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

    /// Invariants.
    pub open spec fn invariants(self) -> bool {
        &&& self.root.level == 0
        &&& self.root.invariants()
    }

    /// Architecture.
    pub open spec fn arch(self) -> PTArch {
        self.root.arch
    }

    /// Map a virtual address to a physical frame.
    ///
    /// If mapping succeeds, return `Ok` and the updated tree.
    pub open spec fn map(self, base: VAddr, frame: Frame) -> Result<Self, ()>
        recommends
            self.invariants(),
            self.arch().is_valid_frame_size(frame.size),
            base.aligned(frame.size.as_nat()),
            frame.base.aligned(frame.size.as_nat()),
    {
        let path = PTTreePath::from_vaddr(
            base,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        let entry = NodeEntry::Frame(frame);
        // Check if already mapped
        let visited = self.root.recursive_visit(path);
        if visited.last() is Empty {
            Ok(Self::new(self.root.recursive_insert(path, entry)))
        } else {
            Err(())
        }
    }

    /// Unmap a virtual address.
    ///
    /// If unmapping succeeds, return `Ok` and the updated tree.
    pub open spec fn unmap(self, base: VAddr) -> Result<Self, ()>
        recommends
            self.invariants(),
    {
        // Check if already mapped
        if let Ok((_, frame)) = self.query(base) {
            // `path` is the right path to the target entry
            let path = PTTreePath::from_vaddr(
                base,
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
                (self.root.arch.vbase_of_va(vaddr, (visited.len() - 1) as nat), frame),
            ),
            _ => Err(()),
        }
    }

    /// Theorem. `map` preserves invariants.
    pub proof fn map_preserves_invariants(self, base: VAddr, frame: Frame)
        requires
            self.invariants(),
            self.arch().is_valid_frame_size(frame.size),
            base.aligned(frame.size.as_nat()),
            frame.base.aligned(frame.size.as_nat()),
        ensures
            self.map(base, frame) is Ok ==> self.map(base, frame).unwrap().invariants(),
    {
        let path = PTTreePath::from_vaddr(
            base,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        // Prove `path` is valid
        PTTreePath::lemma_from_vaddr_valid(
            base,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        self.root.lemma_recursive_insert_preserves_invariants(path, NodeEntry::Frame(frame));
    }

    /// Theorem. `unmap` preserves invariants.
    pub proof fn unmap_preserves_invariants(self, base: VAddr)
        requires
            self.invariants(),
        ensures
            self.unmap(base) is Ok ==> self.unmap(base).unwrap().invariants(),
    {
        let path = PTTreePath::from_vaddr(
            base,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        PTTreePath::lemma_from_vaddr_valid(
            base,
            self.arch(),
            (self.arch().level_count() - 1) as nat,
        );
        let visited = self.root.recursive_visit(path);
        if let NodeEntry::Frame(frame) = visited.last() {
            // There is a mapping with base address `base`

            // The last visited entry satisfies invariants
            self.root.lemma_visited_entries_satisfy_invariants(path);
            assert(self.root.inv_entry(visited.last(), (visited.len() - 1) as nat));
            // Prove `self.arch().level_of_frame_size(frame.size)` will return a valid level
            self.root.lemma_recursive_visit_max_length(path);
            assert(visited.len() - 1 < self.arch().level_count());
            assert(self.arch().is_valid_frame_size(frame.size));
            
            // `path2` is the right path to the target entry
            let path2 = PTTreePath::from_vaddr(
                base,
                self.arch(),
                self.arch().level_of_frame_size(frame.size),
            );
            // Prove `path2` is valid
            PTTreePath::lemma_from_vaddr_valid(
                base,
                self.arch(),
                self.arch().level_of_frame_size(frame.size),
            );
            self.root.lemma_recursive_remove_preserves_invariants(path2);
        }
    }
}

} // verus!
