//! Tree model of the page table.
use vstd::prelude::*;

use crate::spec::{addr::VAddr, arch::PTArch, frame::Frame};

verus! {

/// Represents a path from a node to an entry in the page table tree.
///
/// The path is represented as a sequence of indices, where each index corresponds to
/// an entry in the page table node at a particular level of the hierarchy.
pub struct PTPath(pub Seq<nat>);

impl PTPath {
    /// Path length.
    pub open spec fn len(self) -> nat {
        self.0.len()
    }

    /// Pop head and return the remaining path.
    pub open spec fn step(self) -> (nat, PTPath)
        recommends
            self.len() > 0,
    {
        (self.0[0], PTPath(self.0.skip(1)))
    }

    /// Check if path is valid.
    pub open spec fn valid(self, arch: PTArch, start_level: nat) -> bool {
        &&& self.len() + start_level <= arch.levels()
        &&& forall|i: int|
            0 <= i < self.len() ==> self.0[i] < arch.num_entries(i as nat + start_level)
    }
}

/// Represents a node in the page table tree, which can be either an intermediate node
/// or a leaf node mapping to a physical frame.
pub tracked struct PTTreeNode {
    /// The entries of the node, which can be either sub-nodes, frames, or empty entries.
    pub entries: Seq<NodeEntry>,
    /// The base virtual address of the node, indicating the starting address of the virtual
    /// address range managed by this node.
    pub base: VAddr,
    /// The level of the node in the page table hierarchy.
    pub level: nat,
    /// The architecture of the page table.
    pub arch: PTArch,
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
        self.level == self.arch.levels() - 1
    }

    /// Invariants of an entry in a leaf node.
    pub open spec fn inv_entry_leaf(entry: NodeEntry, arch: PTArch, level: nat) -> bool
        recommends
            level == arch.levels() - 1,
    {
        match entry {
            NodeEntry::Node(_) => false,  // Leaf node cannot have sub-nodes
            NodeEntry::Frame(frame) => {
                &&& frame.size == arch.frame_size(level)
                &&& frame.base.aligned(frame.size.as_nat())
            },
            NodeEntry::Empty => true,
        }
    }

    /// Invariants of an entry in an intermediate node.
    pub open spec fn inv_entry_interm(entry: NodeEntry, arch: PTArch, level: nat) -> bool
        recommends
            level < arch.levels() - 1,
    {
        match entry {
            NodeEntry::Node(node) => {
                &&& node.level == level + 1
                &&& node.arch == arch
            },
            NodeEntry::Frame(frame) => {
                &&& frame.size == arch.frame_size(level)
                &&& frame.base.aligned(frame.size.as_nat())
            },
            NodeEntry::Empty => true,
        }
    }

    /// Invariants of an entry in the node at the specified level.
    pub open spec fn inv_entry(entry: NodeEntry, arch: PTArch, level: nat) -> bool {
        if level == arch.levels() - 1 {
            Self::inv_entry_leaf(entry, arch, level)
        } else {
            Self::inv_entry_interm(entry, arch, level)
        }
    }

    /// Invariants. Recursively checks the invariants of the node and its sub-nodes.
    pub open spec fn invariants(self) -> bool
        decreases self.arch.levels() - self.level,
    {
        &&& self.level < self.arch.levels()
        &&& self.entries.len() == self.arch.num_entries(self.level)
        &&& forall|entry: NodeEntry| #[trigger]
            self.entries.contains(entry) ==> {
                &&& Self::inv_entry(entry, self.arch, self.level)
                &&& entry is Node ==> entry->Node_0.invariants()
            }
    }

    /// Creates an empty root node.
    pub open spec fn new_root(base: VAddr, arch: PTArch) -> Self {
        Self { entries: seq![NodeEntry::Empty; arch.num_entries(0)], base, level: 0, arch }
    }

    /// Creates an empty node.
    pub open spec fn new(base: VAddr, level: nat, arch: PTArch) -> Self {
        Self { entries: seq![NodeEntry::Empty; arch.num_entries(level)], base, level, arch }
    }

    /// Theorem. `new` function implies invariants.
    pub proof fn new_implies_invariants(base: VAddr, level: nat, arch: PTArch)
        requires
            level < arch.levels(),
        ensures
            Self::new(base, level, arch).invariants(),
    {
    }

    /// Update an entry in the node at the specified index.
    pub open spec fn update(self, index: int, entry: NodeEntry) -> Self
        recommends
            0 <= index < self.entries.len(),
            Self::inv_entry(entry, self.arch, self.level),
    {
        Self { entries: self.entries.update(index, entry), ..self }
    }

    /// Theorem. `update` function preserves invariants.
    pub proof fn update_preserves_invariants(self, index: int, entry: NodeEntry)
        requires
            self.invariants(),
            0 <= index < self.entries.len(),
            Self::inv_entry(entry, self.arch, self.level),
            entry is Node ==> entry->Node_0.invariants(),
        ensures
            self.update(index, entry).invariants(),
    {
        let new = self.update(index, entry);
        assert forall|entry2: NodeEntry| #[trigger]
            new.entries.contains(entry2) implies Self::inv_entry(entry2, self.arch, self.level) by {
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

    /// Visit the tree along `path` and return the sequence of entries visited.
    ///
    /// If a reached entry is `Empty` and `path` is not empty, then the visit
    /// terminates early and returns the sequence of entries visited so far.
    pub open spec fn visit(self, path: PTPath) -> Seq<NodeEntry>
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
                NodeEntry::Node(node) => seq![entry].add(node.visit(remain)),
                _ => seq![entry],
            }
        }
    }

    /// Lemma. Each node visited by `visit` satisfies the invariants.
    proof fn lemma_visited_nodes_satisfy_invariants(self, path: PTPath)
        requires
            self.invariants(),
            path.valid(self.arch, self.level),
        ensures
            forall|entry: NodeEntry| #[trigger]
                self.visit(path).contains(entry) ==> (entry is Node ==> entry->Node_0.invariants()),
        decreases path.len(),
    {
        if path.len() == 0 {
            assert(self.visit(path) === seq![]);
        } else {
            let (idx, remain) = path.step();
            let entry = self.entries[idx as int];
            assert(self.entries.contains(entry));
            assert(Self::inv_entry(entry, self.arch, self.level));
            match entry {
                NodeEntry::Node(node) => {
                    assert(self.visit(path) === seq![entry].add(node.visit(remain)));
                    // Recursively prove `node.visit(remain)`
                    node.lemma_visited_nodes_satisfy_invariants(remain);

                    assert forall|entry2: NodeEntry| #[trigger]
                        self.visit(path).contains(entry2) implies !(entry2 is Node)
                        || entry2->Node_0.invariants() by {
                        if entry2 != entry {
                            // Satisfied because of recursive proof
                            assert(node.visit(remain).contains(entry2));
                        }
                    }
                },
                _ => (),
            }
        }
    }

    /// Recursively update the entry at `path`.
    ///
    /// - If a reached entry is `Empty` or `Frame`, and `path` is not empty, then the update
    ///   will be cancelled and the tree will not be modified.
    pub open spec fn recursive_update(self, path: PTPath, entry: NodeEntry) -> Self
        recommends
            self.invariants(),
            path.valid(self.arch, self.level),
            Self::inv_entry(entry, self.arch, (self.level + path.len() - 1) as nat),
            entry is Node ==> entry->Node_0.invariants(),
        decreases path.len(),
    {
        if path.len() == 0 {
            self
        } else {
            let (idx, remain) = path.step();
            let entry = self.entries[idx as int];
            match entry {
                NodeEntry::Node(node) => self.update(
                    idx as int,
                    NodeEntry::Node(node.recursive_update(remain, entry)),
                ),
                _ => self,
            }
        }
    }

    /// Theorem. `recursive_update` function preserves invariants.
    pub proof fn recursive_update_preserves_invariants(self, path: PTPath, entry: NodeEntry)
        requires
            self.invariants(),
            path.valid(self.arch, self.level),
            Self::inv_entry(entry, self.arch, (self.level + path.len() - 1) as nat),
            entry is Node ==> entry->Node_0.invariants(),
        ensures
            self.recursive_update(path, entry).invariants(),
    {
        // TODO
        assume(false);
    }
}

/// Page table tree model.
pub struct PTTreeModel {
    /// The root node.
    pub root: PTTreeNode,
}

impl PTTreeModel {
    /// Invariants.
    pub open spec fn invariants(self) -> bool {
        self.root.invariants()
    }

    /// Map a virtual address to a physical frame.
    ///
    /// If mapping succeeds, return `Ok` and the updated tree. Otherwise, return `Err` and
    /// the original tree.
    pub open spec fn map(self, vaddr: VAddr, frame: Frame) -> Result<Self, Self>
        recommends
            self.invariants(),
    {
        // TODO
        Err(self)
    }

    /// Unmap a virtual address.
    ///
    /// If unmapping succeeds, return `Ok` and the updated tree. Otherwise, return `Err` and
    /// the original tree.
    pub open spec fn unmap(self, vaddr: VAddr) -> Result<Self, Self>
        recommends
            self.invariants(),
    {
        // TODO
        Err(self)
    }

    /// Query a virtual address, return the mapped physical frame.
    ///
    /// If there is no mapping for the virtual address, return `Err(())`.
    pub open spec fn query(self, vaddr: VAddr) -> Result<(VAddr, Frame), ()>
        recommends
            self.invariants(),
    {
        // TODO
        Err(())
    }
}

} // verus!
