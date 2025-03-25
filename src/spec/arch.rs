//! Page table architecture specifications.
use vstd::prelude::*;

use super::{addr::VAddr, frame::FrameSize, is_pow2};

verus! {

/// Represents a single level in a hierarchical page table structure.
pub struct PTArchLevel {
    /// The number of entries at this level.
    pub num_entries: nat,
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
    pub open spec fn num_entries(self, level: nat) -> nat
        recommends
            level < self.level_count(),
    {
        self.0[level as int].num_entries
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
        self.num_entries(level) * PTE_SIZE
    }

    /// All valid frame sizes in this architecture.
    pub open spec fn valid_frame_sizes(self) -> Set<FrameSize> {
        Seq::new(self.level_count(), |i| self.frame_size(i as nat)).to_set()
    }

    /// Calculates the page table entry index for a virtual address at the specified level.
    pub open spec fn pte_index_of_va(self, vaddr: VAddr, level: nat) -> nat
        recommends
            self.invariants(),
            level < self.level_count(),
    {
        vaddr.0 / self.frame_size(level).as_nat() % self.num_entries(level)
    }

    /// Invariants.
    pub open spec fn invariants(self) -> bool {
        // At least one level.
        &&& self.level_count() >= 1
        // Each level has 2^N entries
        &&& forall|level: nat|
            #![auto]
            level < self.level_count() ==> is_pow2(
                self.num_entries(level),
            )
        // frame_size(N) = frame_size(N+1) * num_entries(N+1)
        &&& forall|level: nat|
            1 <= level < self.level_count() ==> self.frame_size((level - 1) as nat).as_nat()
                == self.frame_size(level).as_nat() * self.num_entries(level)
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
        PTArchLevel { num_entries: 512, frame_size: FrameSize::Size512G },
        PTArchLevel { num_entries: 512, frame_size: FrameSize::Size1G },
        PTArchLevel { num_entries: 512, frame_size: FrameSize::Size2M },
        PTArchLevel { num_entries: 512, frame_size: FrameSize::Size4K },
    ],
);

/// Prove `VMSAV8_S1_ARCH` satisfies its invariants.
pub broadcast proof fn vmsav8_s1_4k_arch_invariants()
    by (nonlinear_arith)
    ensures
        #[trigger] VMSAV8_S1_4K_ARCH.invariants(),
{
    assume(is_pow2(512));
}

} // verus!
