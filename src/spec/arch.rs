//! Page table architecture specifications.
use vstd::prelude::*;

use super::{addr::VAddr, frame::FrameSize};

verus! {

/// Represents a single level in a hierarchical page table structure.
pub struct PTArchLevel {
    /// The number of entries at this level.
    pub entry_count: nat,
    /// Frame size indicated by a block/page descriptor at this level.
    pub frame_size: FrameSize,
}

/// Page table entry size.
pub spec const PTE_SIZE: nat = 8;

/// Complete description of a page table architecture, consisting of multiple
/// hierarchical levels from root (lowest level) to leaf (highest level).
pub struct PTArch(pub Seq<PTArchLevel>);

impl PTArch {
    /// The number of hierarchical levels in the page table.
    pub open spec fn level_count(self) -> nat {
        self.0.len()
    }

    /// The number of entries at a specified level.
    pub open spec fn entry_count(self, level: nat) -> nat
        recommends
            level < self.level_count(),
    {
        self.0[level as int].entry_count
    }

    /// The frame size associated with a block/page descriptor at a given level.
    pub open spec fn frame_size(self, level: nat) -> FrameSize
        recommends
            level < self.level_count(),
    {
        self.0[level as int].frame_size
    }

    /// The size of a leaf frame.
    pub open spec fn leaf_frame_size(self) -> FrameSize {
        self.frame_size((self.level_count() - 1) as nat)
    }

    /// The size of a table at a given level.
    pub open spec fn table_size(self, level: nat) -> nat
        recommends
            level < self.level_count(),
    {
        self.entry_count(level) * PTE_SIZE
    }

    /// Check if `size` is a valid frame size.
    pub open spec fn is_valid_frame_size(self, size: FrameSize) -> bool {
        exists|level: nat| level < self.level_count() && self.frame_size(level) == size
    }

    /// Get the corresponding level of a frame size.
    pub open spec fn level_of_frame_size(self, size: FrameSize) -> nat
        recommends
            self.is_valid_frame_size(size),
    {
        choose|level: nat| level < self.level_count() && self.frame_size(level) == size
    }

    /// Calculates the page table entry index for a virtual address at the specified level.
    pub open spec fn pte_index(self, vaddr: VAddr, level: nat) -> nat
        recommends
            self.valid(),
            level < self.level_count(),
    {
        vaddr.0 / self.frame_size(level).as_nat() % self.entry_count(level)
    }

    /// Check if the page table architecture is valid.
    pub open spec fn valid(self) -> bool {
        // At least one level.
        &&& self.level_count() > 0
        // Entry count > 1.
        &&& forall|level: nat|
            level < self.level_count() ==> self.entry_count(level)
                > 1
            // frame_size(N) = frame_size(N+1) * entry_count(N+1)
        &&& forall|level: nat|
            1 <= level < self.level_count() ==> self.frame_size((level - 1) as nat).as_nat()
                == self.frame_size(level).as_nat() * self.entry_count(level)
    }

    /// Lemma. PTE index is less than entry count.
    pub proof fn lemma_pte_index_less_than_entry_count(self, vaddr: VAddr, level: nat)
        requires
            self.valid(),
            level < self.level_count(),
        ensures
            self.pte_index(vaddr, level) < self.entry_count(level),
    {
    }

    /// Lemma (helper). a > 0, b > 1 implies a * b > a.
    proof fn lemma_mul_gt_one(a: nat, b: nat)
        by (nonlinear_arith)
        requires
            a > 0,
            b > 1,
        ensures
            a * b > a,
    {
    }

    /// Lemma. Frame size decreases as level increases.
    pub proof fn lemma_frame_size_monotonic(self, l1: nat, l2: nat)
        requires
            self.valid(),
            l1 < l2 < self.level_count(),
        ensures
            self.frame_size(l1).as_nat() > self.frame_size(l2).as_nat(),
        decreases l2 - l1,
    {
        if l2 - l1 == 1 {
            assert(self.frame_size(l2).as_nat() > 0);
            assert(self.entry_count(l2) > 1);
            Self::lemma_mul_gt_one(self.frame_size(l2).as_nat(), self.entry_count(l2));
            assert(self.frame_size(l1).as_nat() > self.frame_size(l2).as_nat());
        } else {
            assert(self.frame_size(l1 + 1).as_nat() > 0);
            assert(self.entry_count(l1 + 1) > 1);
            Self::lemma_mul_gt_one(self.frame_size(l1 + 1).as_nat(), self.entry_count(l1 + 1));
            assert(self.frame_size(l1).as_nat() > self.frame_size(l1 + 1).as_nat());
            // Prove monotonicity for (l1, l1 + 1) and (l1 + 1, l2).
            self.lemma_frame_size_monotonic(l1 + 1, l2);
        }
    }

    /// Lemma. level_of_frame_size(frame_size(level)) == level.
    pub proof fn lemma_frame_size_inversion(self, level: nat)
        requires
            self.valid(),
            level < self.level_count(),
        ensures
            self.level_of_frame_size(self.frame_size(level)) == level,
    {
        let level2 = self.level_of_frame_size(self.frame_size(level));
        if level2 < level {
            self.lemma_frame_size_monotonic(level2, level);
        } else if level2 > level {
            self.lemma_frame_size_monotonic(level, level2);
        }
    }
}

/// For VMSAv8-64 using 4K granule. The architecture is specified as follows:
///
/// | Level | Index into PT | Entry Num |  Entry Type  | Frame Size |
/// |-------|---------------|-----------|--------------|------------|
/// | 0     | 47:39         | 512       | Table        | 512G       |
/// | 1     | 38:30         | 512       | Table/Block  | 1G         |
/// | 2     | 29:21         | 512       | Table/Block  | 2M         |
/// | 3     | 20:12         | 512       | Page         | 4K         |
///
/// *If effective value of TCR_ELx.DS is 0, level 0 allows Table descriptor only.
pub spec const VMSAV8_4K_ARCH: PTArch = PTArch(
    seq![
        PTArchLevel { entry_count: 512, frame_size: FrameSize::Size512G },
        PTArchLevel { entry_count: 512, frame_size: FrameSize::Size1G },
        PTArchLevel { entry_count: 512, frame_size: FrameSize::Size2M },
        PTArchLevel { entry_count: 512, frame_size: FrameSize::Size4K },
    ],
);

/// `VMSAV8_4K_ARCH` is a valid architecture.
pub proof fn lemma_vmsav8_4k_arch_valid()
    by (nonlinear_arith)
    ensures
        VMSAV8_4K_ARCH.valid(),
{
}

} // verus!
