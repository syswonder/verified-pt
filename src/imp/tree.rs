//! Tree model of the page table.

use vstd::prelude::*;

use crate::spec::{
    frame::Frame,
    addr::VAddr,
};

verus! {

/// Represents a node in the page table tree, which can be either an intermediate node
/// or a leaf node mapping to a physical frame.
pub struct PTTreeNode {
    /// The centries of the node, which can be either sub-nodes, frames, or empty entries.
    pub entries: Seq<NodeEntry>,
    /// The base virtual address of the node, indicating the starting address of the virtual
    /// address range managed by this node.
    pub base: VAddr,
    /// The level of the node in the page table hierarchy.
    pub level: nat,
}

/// Represents an entry in the page table node, which can be a sub-node, a physical frame,
/// or an empty entry.
pub enum NodeEntry {
    /// A sub-node in the page table, representing an intermediate level of the page table hierarchy.
    Node(PTTreeNode),
    /// A physical frame mapped by the node, representing a leaf node in the page table tree.
    Frame(Frame),
    /// An empty entry in the page table, indicating that the corresponding virtual address range
    /// is not currently mapped or allocated.
    Empty,
}

impl PTTreeNode {
    /// Invariants.
    pub open spec fn invariants(self) -> bool {
        true
    }

    /// Creates an empty node.
    pub open spec fn new(base: VAddr, level: nat) -> Self {
        Self { entries: Seq::empty(), base, level }
    }

    /// Theorem. `new` function implies invariants.
    pub proof fn new_implies_invariants(base: VAddr, level: nat) {
        assert(Self::new(base, level).invariants());
    }

    /// Insert an entry into the node at the specified index.
    pub open spec fn insert(self, index: int, entry: NodeEntry) -> Self {
        Self { entries: self.entries.update(index, entry), ..self }
    }

    /// Theorem. `insert` function preserves invariants.
    pub proof fn insert_preserves_invariants(self, index: int, entry: NodeEntry)
        requires
            self.invariants(),
        ensures
            self.insert(index, entry).invariants(),
    {
    }

    /// Remove an entry from the node at the specified index.
    pub open spec fn remove(self, index: int) -> Self {
        Self { entries: self.entries.remove(index), ..self }
    }

    /// Theorem. `remove` function preserves invariants.
    pub proof fn remove_preserves_invariants(self, index: int)
        requires
            self.invariants(),
        ensures
            self.remove(index).invariants(),
    {
    }
}

} // verus!