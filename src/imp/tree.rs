//! Tree model of the page table.
use vstd::prelude::*;

use crate::spec::{
    addr::{PAddr, VAddr},
    arch::PTArch,
    frame::Frame,
    pt_spec::{PTConstants, PageTableState},
};

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

    /// Trim the path to the given length.
    pub open spec fn trim(self, len: nat) -> PTTreePath
        recommends
            len <= self.len(),
    {
        PTTreePath(self.0.take(len as int))
    }

    /// Check if path is valid.
    pub open spec fn valid(self, arch: PTArch, start_level: nat) -> bool
        recommends
            arch.valid(),
    {
        &&& self.len() > 0
        &&& self.len() + start_level <= arch.level_count()
        &&& forall|i: int|
            0 <= i < self.len() ==> self.0[i] < arch.entry_count(i as nat + start_level)
    }

    /// If `self` has a non-empty prefix `p`.
    pub open spec fn has_prefix(self, p: PTTreePath) -> bool {
        &&& 0 < p.len() <= self.len()
        &&& forall|i: int| 0 <= i < p.len() ==> self.0[i] == p.0[i]
    }

    /// Get the first position at which two paths differ.
    pub open spec fn first_diff_idx(a: PTTreePath, b: PTTreePath) -> int
        recommends
            a.len() > 0,
            b.len() > 0,
            !a.has_prefix(b),
            !b.has_prefix(a),
    {
        choose|i: int|
            0 <= i < a.len() && i < b.len() && a.0[i] != b.0[i] && forall|j: int|
                0 <= j < i ==> a.0[j] == b.0[j]
    }

    /// Get a `PTTreePath` from a virtual address, used to query the page table from root.
    ///
    /// The last query level of the returned path is `level`, and the path length is `level + 1`.
    pub open spec fn from_vaddr(vaddr: VAddr, arch: PTArch, level: nat) -> PTTreePath
        recommends
            arch.valid(),
            level < arch.level_count(),
    {
        PTTreePath(Seq::new(level + 1, |i: int| arch.pte_index_of_va(vaddr, i as nat)))
    }

    /// Calculate the virtual address corresponding to the path from root.
    pub open spec fn to_vaddr(self, arch: PTArch) -> VAddr
        recommends
            arch.valid(),
            self.valid(arch, 0),
    {
        let parts: Seq<nat> = Seq::new(
            self.len(),
            |i: int| self.0[i] * arch.frame_size(i as nat).as_nat(),
        );
        VAddr(parts.fold_left(0nat, |sum: nat, part| sum + part))
    }

    /// Lemma. A prefix of a valid path is also valid.
    pub proof fn lemma_prefix_valid(self, arch: PTArch, start_level: nat, prefix: PTTreePath)
        requires
            arch.valid(),
            self.valid(arch, start_level),
            self.has_prefix(prefix),
        ensures
            prefix.valid(arch, start_level),
    {
    }

    /// Lemma. If a prefix has the same length as the full path, then the two paths are equal.
    pub proof fn lemma_prefix_equals_full(self, prefix: PTTreePath)
        requires
            self.has_prefix(prefix),
            prefix.len() == self.len(),
        ensures
            self == prefix,
    {
        assert(self.0 == prefix.0);
    }

    /// Lemma. Existence of the first differing index between two distinct paths.
    pub proof fn lemma_first_diff_idx_exists(a: PTTreePath, b: PTTreePath)
        requires
            a.len() > 0,
            b.len() > 0,
            !a.has_prefix(b),
            !b.has_prefix(a),
        ensures
            exists|i: int|
                0 <= i < a.len() && i < b.len() && a.0[i] != b.0[i] && forall|j: int|
                    0 <= j < i ==> a.0[j] == b.0[j],
    {
        assert(exists|i: int| 0 <= i < a.len() && i < b.len() && a.0[i] != b.0[i]);
        let i = choose|i: int| 0 <= i < a.len() && i < b.len() && a.0[i] != b.0[i];
        Self::lemma_first_diff_idx_exists_recursive(a, b, i);
    }

    /// Helper lemma to prove `lemma_first_diff_idx_exists` by induction.
    proof fn lemma_first_diff_idx_exists_recursive(a: PTTreePath, b: PTTreePath, i: int)
        requires
            a.len() > 0,
            b.len() > 0,
            !a.has_prefix(b),
            !b.has_prefix(a),
            0 <= i < a.len() && i < b.len() && a.0[i] != b.0[i],
        ensures
            exists|j: int|
                0 <= j <= i && a.0[j] != b.0[j] && forall|k: int| 0 <= k < j ==> a.0[k] == b.0[k],
        decreases i,
    {
        if exists|j: int| 0 <= j < i && a.0[j] != b.0[j] {
            let j = choose|j: int| 0 <= j < i && a.0[j] != b.0[j];
            Self::lemma_first_diff_idx_exists_recursive(a, b, j);
        } else {
            assert(forall|k: int| 0 <= k < i ==> a.0[k] == b.0[k]);
        }
    }

    /// Lemma. `from_vaddr` produces a valid path rooted at level 0.
    pub proof fn lemma_from_vaddr_yields_valid_path(vaddr: VAddr, arch: PTArch, level: nat)
        requires
            level < arch.level_count(),
            arch.valid(),
        ensures
            PTTreePath::from_vaddr(vaddr, arch, level).valid(arch, 0),
    {
        let path = PTTreePath::from_vaddr(vaddr, arch, level);
        assert forall|i: int| 0 <= i < path.len() implies path.0[i] < arch.entry_count(
            i as nat,
        ) by {
            // TODO: Verus cannot imply (a % b) < b
            // See: https://verus-lang.github.io/verus/guide/nonlinear.html
            assume(arch.pte_index_of_va(vaddr, i as nat) < arch.entry_count(i as nat))
        }
    }

    /// Lemma. The address computed by `to_vaddr` is aligned to the frame size of the last level.
    pub proof fn lemma_to_vaddr_frame_alignment(self, arch: PTArch)
        by (nonlinear_arith)
        requires
            arch.valid(),
            self.valid(arch, 0),
        ensures
            self.to_vaddr(arch).aligned(arch.frame_size((self.len() - 1) as nat).as_nat()),
    {
        let parts: Seq<nat> = Seq::new(
            self.len(),
            |i: int| self.0[i] * arch.frame_size(i as nat).as_nat(),
        );
        // TODO: This is true by arch.valid(). Recursive proof is needed.
        assume(forall|i|
            0 <= i < self.len() ==> #[trigger] arch.frame_size(i).as_nat() % arch.frame_size(
                (self.len() - 1) as nat,
            ).as_nat() == 0);
        assert(forall|i|
            0 <= i < self.len() ==> parts[i] % arch.frame_size((self.len() - 1) as nat).as_nat()
                == 0);
        let sum = parts.fold_left(0nat, |sum: nat, part| sum + part);
        // TODO: All parts align to the frame size of the last level, prove that sum does too.
        assume(sum % arch.frame_size((self.len() - 1) as nat).as_nat() == 0);
    }

    /// Lemma. If `path` has a prefix `prefix`, then `path.to_vaddr()` has a maximum and a minimum.
    pub proof fn lemma_to_vaddr_bounds(arch: PTArch, path: PTTreePath, prefix: PTTreePath)
        requires
            arch.valid(),
            path.valid(arch, 0),
            path.has_prefix(prefix),
        ensures
            prefix.to_vaddr(arch).0 <= path.to_vaddr(arch).0 <= prefix.to_vaddr(arch).0
                + arch.frame_size((prefix.len() - 1) as nat).as_nat() - arch.frame_size(
                (path.len() - 1) as nat,
            ).as_nat(),
    {
        // TODO
        assume(false);
    }

    /// Lemma. If two paths `a` and `b` differ at index `first_diff_idx`, then the virtual address
    /// of `a` plus one frame is below that of `b`.
    pub proof fn lemma_path_order_implies_vaddr_order(arch: PTArch, a: PTTreePath, b: PTTreePath)
        requires
            arch.valid(),
            a.valid(arch, 0),
            b.valid(arch, 0),
            !a.has_prefix(b),
            !b.has_prefix(a),
            a.0[PTTreePath::first_diff_idx(a, b)] < b.0[PTTreePath::first_diff_idx(a, b)],
        ensures
            a.to_vaddr(arch).0 + arch.frame_size((a.len() - 1) as nat).as_nat() <= b.to_vaddr(
                arch,
            ).0,
    {
        // Trim the paths at the first differing index
        PTTreePath::lemma_first_diff_idx_exists(a, b);
        let diff_idx = PTTreePath::first_diff_idx(a, b);
        let pref_a = a.trim((diff_idx + 1) as nat);
        let pref_b = b.trim((diff_idx + 1) as nat);

        // Bound the full paths by their prefixes
        PTTreePath::lemma_to_vaddr_bounds(arch, a, pref_a);
        PTTreePath::lemma_to_vaddr_bounds(arch, b, pref_b);
        assert(a.to_vaddr(arch).0 + arch.frame_size((a.len() - 1) as nat).as_nat()
            <= pref_a.to_vaddr(arch).0 + arch.frame_size((pref_a.len() - 1) as nat).as_nat());
        assert(pref_b.to_vaddr(arch).0 <= b.to_vaddr(arch).0);

        // `common` is the same part shared by `pref_a` and `pref_b`
        assert(pref_a.trim(diff_idx as nat).0 == pref_b.trim(diff_idx as nat).0);
        let common = pref_a.trim(diff_idx as nat);

        // Show `common_parts` is equally added when computing vaddr
        let common_parts = Seq::new(
            common.len(),
            |i: int| common.0[i] * arch.frame_size(i as nat).as_nat(),
        );
        let pref_a_parts = Seq::new(
            pref_a.len(),
            |i: int| pref_a.0[i] * arch.frame_size(i as nat).as_nat(),
        );
        let pref_b_parts = Seq::new(
            pref_b.len(),
            |i: int| pref_b.0[i] * arch.frame_size(i as nat).as_nat(),
        );
        assert(pref_a_parts.take(diff_idx) == common_parts);
        assert(pref_a_parts.fold_left(0, |sum: nat, part| sum + part) == common_parts.fold_left(
            0nat,
            |sum: nat, part| sum + part,
        ) + pref_a.0[diff_idx] * arch.frame_size(diff_idx as nat).as_nat());
        assert(pref_b_parts.take(diff_idx) == common_parts);
        assert(pref_b_parts.fold_left(0, |sum: nat, part| sum + part) == common_parts.fold_left(
            0nat,
            |sum: nat, part| sum + part,
        ) + pref_b.0[diff_idx] * arch.frame_size(diff_idx as nat).as_nat());

        // Extract the sum as "common parts" + "difference part"
        assert(pref_a.to_vaddr(arch).0 == common.to_vaddr(arch).0 + pref_a.0[diff_idx]
            * arch.frame_size(diff_idx as nat).as_nat());
        assert(pref_b.to_vaddr(arch).0 == common.to_vaddr(arch).0 + pref_b.0[diff_idx]
            * arch.frame_size(diff_idx as nat).as_nat());

        // Calculate the minimum difference between `pref_a.to_vaddr()` and `pref_b.to_vaddr()`
        assert(pref_b.to_vaddr(arch).0 - pref_a.to_vaddr(arch).0 == (pref_b.0[diff_idx]
            - pref_a.0[diff_idx]) * arch.frame_size(diff_idx as nat).as_nat());
        assert(pref_b.0[diff_idx] - pref_a.0[diff_idx] >= 1);
        assert(pref_b.to_vaddr(arch).0 - pref_a.to_vaddr(arch).0 >= arch.frame_size(
            diff_idx as nat,
        ).as_nat());

        // Prove the bounded inequality
        assert(a.to_vaddr(arch).0 + arch.frame_size((a.len() - 1) as nat).as_nat() <= b.to_vaddr(
            arch,
        ).0);
    }
}

/// Represents a node in the page table tree, which can be either an intermediate node
/// or a leaf node mapping to a physical frame.
pub tracked struct PTTreeNode {
    /// Page table configuration.
    pub config: PTConfig,
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

/// Page table configuration.
pub struct PTConfig {
    /// The architecture of the page table.
    pub arch: PTArch,
    /// Physical memory lower bound.
    pub pmem_lb: PAddr,
    /// Physical memory upper bound.
    pub pmem_ub: PAddr,
}

impl PTTreeNode {
    /// If the node is a leaf node.
    pub open spec fn is_leaf(self) -> bool {
        self.level == self.config.arch.level_count() - 1
    }

    /// Invariants of a node entry at the specified level under the given configuration.
    pub open spec fn inv_entry(entry: NodeEntry, level: nat, config: PTConfig) -> bool
        recommends
            level < config.arch.level_count(),
    {
        match entry {
            NodeEntry::Node(node) => if level < config.arch.level_count() - 1 {
                &&& node.level == level
                    + 1
                // All nodes share the same configuration.
                &&& node.config == config
            } else {
                false
            },
            NodeEntry::Frame(frame) => {
                &&& frame.size == config.arch.frame_size(level)
                &&& frame.base.aligned(frame.size.as_nat())
                &&& frame.base.0 >= config.pmem_lb.0
                &&& frame.base.0 + frame.size.as_nat() <= config.pmem_ub.0
            },
            NodeEntry::Empty => true,
        }
    }

    /// Invariants. Recursively checks the invariants of the node and its sub-nodes.
    ///
    /// This ensures a sub-tree is well-formed, and all mappings are valid and aligned.
    pub open spec fn invariants(self) -> bool
        decreases self.config.arch.level_count() - self.level,
    {
        &&& self.config.arch.valid()
        &&& self.level < self.config.arch.level_count()
        &&& self.entries.len() == self.config.arch.entry_count(self.level)
        &&& forall|entry: NodeEntry| #[trigger]
            self.entries.contains(entry) ==> {
                &&& Self::inv_entry(entry, self.level, self.config)
                &&& entry is Node ==> entry->Node_0.invariants()
            }
    }

    /// Creates an empty node.
    pub open spec fn new(config: PTConfig, level: nat) -> Self
        recommends
            level < config.arch.level_count(),
            config.arch.valid(),
    {
        Self { config, level, entries: seq![NodeEntry::Empty; config.arch.entry_count(level)] }
    }

    /// Update an entry in the node at the specified index.
    pub open spec fn update(self, index: nat, entry: NodeEntry) -> Self
        recommends
            index < self.entries.len(),
            Self::inv_entry(entry, self.level, self.config),
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
            path.valid(self.config.arch, self.level),
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        if path.len() <= 1 {
            seq![entry]
        } else {
            match entry {
                NodeEntry::Node(node) => seq![entry].add(node.recursive_visit(remain)),
                _ => seq![entry],
            }
        }
    }

    /// Returns the longest prefix of `path` that can reach an entry without early terminating.
    pub open spec fn real_path(self, path: PTTreePath) -> PTTreePath
        recommends
            self.invariants(),
            path.valid(self.config.arch, self.level),
    {
        path.trim(self.recursive_visit(path).len())
    }

    /// Inserts a sub-node or frame at `path`, creating intermediate nodes if needed.
    ///
    /// Does nothing if target slot is non-empty.
    pub open spec fn recursive_insert(self, path: PTTreePath, entry: NodeEntry) -> Self
        recommends
            self.invariants(),
            path.valid(self.config.arch, self.level),
            entry is Node || entry is Frame,
            Self::inv_entry(entry, (self.level + path.len() - 1) as nat, self.config),
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
                        PTTreeNode::new(self.config, self.level + 1).recursive_insert(
                            remain,
                            entry,
                        ),
                    ),
                ),
                _ => self,
            }
        }
    }

    /// Removes any entry at `path` by setting it to `Empty`.
    ///
    /// Does nothing if the entry at `path` is already `Empty`.
    pub open spec fn recursive_remove(self, path: PTTreePath) -> Self
        recommends
            self.invariants(),
            path.valid(self.config.arch, self.level),
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

    /// Lemma. `new` implies invariants.
    pub proof fn lemma_new_implies_invariants(config: PTConfig, level: nat)
        requires
            level < config.arch.level_count(),
            config.arch.valid(),
        ensures
            Self::new(config, level).invariants(),
    {
    }

    /// Lemma. Length of `recursive_visit(path)` is between 1 and `path.len()`.
    proof fn lemma_visit_length_bounds(self, path: PTTreePath)
        requires
            self.invariants(),
            path.valid(self.config.arch, self.level),
        ensures
            1 <= self.recursive_visit(path).len() <= path.len(),
        decreases path.len(),
    {
        if path.len() <= 1 {
            assert(self.recursive_visit(path).len() == 1);
        } else {
            let (idx, remain) = path.step();
            let entry = self.entries[idx as int];
            assert(self.entries.contains(entry));
            match entry {
                NodeEntry::Node(node) => {
                    node.lemma_visit_length_bounds(remain);
                },
                _ => assert(self.recursive_visit(path).len() == 1),
            }
        }
    }

    /// Lemma. Every entry returned by `recursive_visit` satisfies `inv_entry`.
    pub proof fn lemma_visited_entries_satisfy_invariants(self, path: PTTreePath)
        requires
            self.invariants(),
            path.valid(self.config.arch, self.level),
        ensures
            forall|i: int|
                #![auto]
                0 <= i < self.recursive_visit(path).len() ==> Self::inv_entry(
                    self.recursive_visit(path)[i],
                    self.level + i as nat,
                    self.config,
                ),
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));
        assert(Self::inv_entry(entry, self.level, self.config));
        if path.len() > 1 {
            match entry {
                NodeEntry::Node(node) => {
                    assert(self.recursive_visit(path) === seq![entry].add(
                        node.recursive_visit(remain),
                    ));
                    // Recursively prove `node.recursive_visit(remain)` satisfies the invariants
                    node.lemma_visited_entries_satisfy_invariants(remain);
                },
                _ => (),
            }
        }
    }

    /// Lemma. All visited entries except the final one must be sub-nodes.
    proof fn lemma_visited_entry_is_node_except_final(self, path: PTTreePath)
        requires
            self.invariants(),
            path.valid(self.config.arch, self.level),
        ensures
            forall|i|
                0 <= i < self.recursive_visit(path).len() - 1 ==> self.recursive_visit(
                    path,
                )[i] is Node,
        decreases path.len(),
    {
        let (idx, remain) = path.step();
        let entry = self.entries[idx as int];
        assert(self.entries.contains(entry));
        assert(Self::inv_entry(entry, self.level, self.config));
        if path.len() > 1 {
            match entry {
                NodeEntry::Node(node) => {
                    assert(self.recursive_visit(path) === seq![entry].add(
                        node.recursive_visit(remain),
                    ));
                    // Recursively prove `node.recursive_visit(remain)`
                    node.lemma_visited_entry_is_node_except_final(remain);
                },
                _ => (),
            }
        }
    }

    /// Lemma. If `prefix` is a prefix of `path`, then the visit sequence of `prefix`
    /// is a prefix of that of `path`.
    proof fn lemma_visit_preserves_prefix(self, path: PTTreePath, prefix: PTTreePath)
        requires
            self.invariants(),
            path.valid(self.config.arch, self.level),
            path.has_prefix(prefix),
        ensures
            self.recursive_visit(prefix).len() <= self.recursive_visit(path).len(),
            forall|i|
                0 <= i < self.recursive_visit(prefix).len() ==> self.recursive_visit(prefix)[i]
                    === self.recursive_visit(path)[i],
        decreases path.len(),
    {
        let visited = self.recursive_visit(path);
        let p_visited = self.recursive_visit(prefix);
        let (idx, remain) = path.step();
        let (p_idx, p_remain) = prefix.step();
        assert(p_idx == idx);
        let entry = self.entries[p_idx as int];
        assert(self.entries.contains(entry));

        if prefix.len() > 1 {
            match entry {
                NodeEntry::Node(node) => {
                    assert(visited == seq![entry].add(node.recursive_visit(remain)));
                    assert(p_visited == seq![entry].add(node.recursive_visit(p_remain)));
                    // Recursively prove `node.recursive_visit(remain)`
                    node.lemma_visit_preserves_prefix(remain, p_remain);
                    assert forall|i| 0 < i < p_visited.len() implies p_visited[i] == visited[i] by {
                        assert(p_visited[i] == node.recursive_visit(p_remain)[i - 1]);
                        assert(visited[i] == node.recursive_visit(remain)[i - 1]);
                    }
                },
                _ => (),
            }
        }
    }

    /// Lemma. The entry sequence visited by `path` and `real_path(path)` are the same.
    pub proof fn lemma_real_path_visits_same_entry(self, path: PTTreePath)
        requires
            self.invariants(),
            path.valid(self.config.arch, self.level),
        ensures
            self.recursive_visit(self.real_path(path)) == self.recursive_visit(path),
        decreases path.len(),
    {
        let r_path = self.real_path(path);
        let visited = self.recursive_visit(path);
        let r_visited = self.recursive_visit(r_path);

        let (idx, remain) = path.step();
        let (r_idx, r_remain) = r_path.step();
        self.lemma_visit_length_bounds(path);
        self.lemma_visit_length_bounds(r_path);
        assert(idx == r_idx);
        let entry = self.entries[r_idx as int];
        assert(self.entries.contains(entry));

        if r_path.len() <= 1 {
            assert(r_visited == seq![entry]);
            assert(visited == seq![entry]);
        } else {
            match entry {
                NodeEntry::Node(node) => {
                    assert(r_visited == seq![entry].add(node.recursive_visit(r_remain)));
                    assert(visited == seq![entry].add(node.recursive_visit(remain)));
                    // Prove `r_remain` is the real path of `remain`
                    assert(node.real_path(remain).0 == path.0.skip(1).take(visited.len() - 1));
                    assert(r_remain.0 == path.0.skip(1).take(visited.len() - 1));
                    assert(r_remain == node.real_path(remain));
                    // Recursively prove `node.recursive_visit(remain)`
                    node.lemma_real_path_visits_same_entry(remain);
                },
                _ => {
                    assert(r_visited == seq![entry]);
                    assert(visited == seq![entry]);
                },
            }
        }
    }

    /// Lemma. `update` preserves invariants.
    pub proof fn lemma_update_preserves_invariants(self, index: nat, entry: NodeEntry)
        requires
            self.invariants(),
            0 <= index < self.entries.len(),
            Self::inv_entry(entry, self.level, self.config),
            entry is Node ==> entry->Node_0.invariants(),
        ensures
            self.update(index, entry).invariants(),
    {
        let new = self.update(index, entry);
        assert forall|entry2: NodeEntry| #[trigger]
            new.entries.contains(entry2) implies Self::inv_entry(
            entry2,
            self.level,
            self.config,
        ) by {
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

    /// Lemma. `recursive_insert` preserves invariants.
    pub proof fn lemma_insert_preserves_invariants(self, path: PTTreePath, entry: NodeEntry)
        requires
            self.invariants(),
            path.len() > 0,
            path.valid(self.config.arch, self.level),
            entry is Node || entry is Frame,
            Self::inv_entry(entry, (self.level + path.len() - 1) as nat, self.config),
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
                    assert(Self::inv_entry(entry2, self.level, self.config));
                    assert(node.invariants());
                    // Recursively prove `node.recursive_insert(remain)`
                    node.lemma_insert_preserves_invariants(remain, entry);
                    // `node.recursive_update(remain, entry)` satisfies invariants,
                    // so the updated `self` also satisfy invariants by lemma
                    self.lemma_update_preserves_invariants(
                        idx,
                        NodeEntry::Node(node.recursive_insert(remain, entry)),
                    );
                },
                NodeEntry::Empty => {
                    let new = PTTreeNode::new(self.config, self.level + 1);
                    // `new` satisfies invariants by construction
                    assert(new.invariants());
                    // Recursively prove `new.recursive_insert(remain)`
                    new.lemma_insert_preserves_invariants(remain, entry);
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

    /// Lemma. `recursive_remove` preserves invariants.
    pub proof fn lemma_remove_preserves_invariants(self, path: PTTreePath)
        requires
            self.invariants(),
            path.len() > 0,
            path.valid(self.config.arch, self.level),
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
                    assert(Self::inv_entry(entry2, self.level, self.config));
                    assert(node.invariants());
                    // Recursively prove `node.recursive_remove(remain)`
                    node.lemma_remove_preserves_invariants(remain);
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
    {
        let path = PTTreePath::from_vaddr(
            vbase,
            self.arch(),
            self.arch().level_of_frame_size(frame.size),
        );
        // Check if already mapped
        let visited = self.root.recursive_visit(path);
        if visited.last() is Empty {
            Ok(Self::new(self.root.recursive_insert(path, NodeEntry::Frame(frame))))
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
            assert(PTTreeNode::inv_entry(
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
        ensures
            self.map(vbase, frame) is Ok ==> self.map(vbase, frame).unwrap().mappings()
                === self.mappings().insert(vbase, frame),
    {
        // TODO
        assume(false);
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
        self.root.lemma_insert_preserves_invariants(path, NodeEntry::Frame(frame));
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
            assert(PTTreeNode::inv_entry(
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
