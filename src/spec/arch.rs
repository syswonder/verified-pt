//! Page table architecture specifications.
use vstd::prelude::*;

use super::{addr::VAddr, frame::FrameSize};

verus! {

/// Represents a single level in a hierarchical page table structure.
pub struct PTArchLevel {
    /// log2 of the number of entries at this level.
    pub entry_count_log2: nat,
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
        (1 << self.0[level as int].entry_count_log2) as nat
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
    pub open spec fn pte_index_of_va(self, vaddr: VAddr, level: nat) -> nat
        recommends
            self.valid(),
            level < self.level_count(),
    {
        vaddr.0 / self.frame_size(level).as_nat() % self.entry_count(level)
    }

    /// Calculates the virtual page base address that contains a given virtual address at the specified level.
    pub open spec fn vbase_of_va(self, vaddr: VAddr, level: nat) -> VAddr
        recommends
            self.valid(),
            level < self.level_count(),
    {
        VAddr((vaddr.0 - vaddr.0 % self.frame_size(level).as_nat()) as nat)
    }

    /// Check if the page table architecture is valid.
    pub open spec fn valid(self) -> bool {
        // At least one level.
        &&& self.level_count()
            > 0
        // frame_size(N) = frame_size(N+1) * entry_count(N+1)
        &&& forall|level: nat|
            1 <= level < self.level_count() ==> self.frame_size((level - 1) as nat).as_nat()
                == self.frame_size(level).as_nat() * self.entry_count(level)
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
pub spec const VMSAV8_S1_4K_ARCH: PTArch = PTArch(
    seq![
        PTArchLevel { entry_count_log2: 9, frame_size: FrameSize::Size512G },
        PTArchLevel { entry_count_log2: 9, frame_size: FrameSize::Size1G },
        PTArchLevel { entry_count_log2: 9, frame_size: FrameSize::Size2M },
        PTArchLevel { entry_count_log2: 9, frame_size: FrameSize::Size4K },
    ],
);

/// Prove `VMSAV8_S1_ARCH` satisfies its invariants.
pub broadcast proof fn vmsav8_s1_4k_arch_invariants()
    by (nonlinear_arith)
    ensures
        #[trigger] VMSAV8_S1_4K_ARCH.valid(),
{
    assume(1 << 9 == 512);
}

} // verus!
