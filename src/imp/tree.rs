//! Tree model of the page table.
use vstd::prelude::*;

use crate::spec::{addr::VAddr, arch::PTArch, frame::Frame};

verus! {

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
    pub open spec fn inv_entry_leaf(self, entry: NodeEntry) -> bool
        recommends
            self.is_leaf(),
    {
        match entry {
            NodeEntry::Node(_) => false,  // Leaf node cannot have sub-nodes
            NodeEntry::Frame(frame) => {
                &&& frame.size == self.arch.frame_size(self.level)
                &&& frame.base.aligned(frame.size.as_nat())
            },
            NodeEntry::Empty => true,
        }
    }

    /// Invariants of an entry in an intermediate node.
    pub open spec fn inv_entry_interm(self, entry: NodeEntry) -> bool
        recommends
            !self.is_leaf(),
    {
        match entry {
            NodeEntry::Node(node) => {
                &&& node.level == self.level + 1
                &&& node.arch == self.arch
            },
            NodeEntry::Frame(frame) => {
                &&& frame.size == self.arch.frame_size(self.level)
                &&& frame.base.aligned(frame.size.as_nat())
            },
            NodeEntry::Empty => true,
        }
    }

    /// Invariants of an entry in the node.
    pub open spec fn inv_entry(self, entry: NodeEntry) -> bool {
        if self.is_leaf() {
            self.inv_entry_leaf(entry)
        } else {
            self.inv_entry_interm(entry)
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
                &&& self.inv_entry(entry)
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
            self.inv_entry(entry),
    {
        Self { entries: self.entries.update(index, entry), ..self }
    }

    /// Theorem. `update` function preserves invariants.
    pub proof fn update_preserves_invariants(self, index: int, entry: NodeEntry)
        requires
            self.invariants(),
            0 <= index < self.entries.len(),
            self.inv_entry(entry),
            entry is Node ==> entry->Node_0.invariants(),
        ensures
            self.update(index, entry).invariants(),
    {
        let new = self.update(index, entry);
        assert forall|entry2: NodeEntry| #[trigger]
            new.entries.contains(entry2) implies new.inv_entry(entry2) by {
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
}

} // verus!
