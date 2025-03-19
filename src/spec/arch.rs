//! Page table architecture specifications.
use vstd::prelude::*;

use super::frame::FrameSize;

verus! {

/// Page table architecture level.
pub struct PTArchLevel {
    /// The number of entries at this level.
    pub num_entries: nat,
    /// Frame size indicated by a block/page descriptor at this level.
    pub frame_size: FrameSize,
}

/// Page table architecture.
pub struct PTArch(pub Seq<PTArchLevel>);

impl PTArch {
    /// The number of levels in the page table.
    pub open spec fn levels(&self) -> nat {
        self.0.len()
    }

    /// The number of entries at a given level.
    pub open spec fn num_entries(&self, level: nat) -> nat {
        self.0[level as int].num_entries
    }

    /// The frame size indicated by a block/page descriptor at a given level.
    pub open spec fn frame_size(&self, level: nat) -> FrameSize {
        self.0[level as int].frame_size
    }
}

/// For VMSAv8-64 using 4K granule. The architecture is specified as follows:
///
/// | Level | Index into PT | Entry Num |  Entry Type  | Frame Size |
/// |-------|---------------|-----------|--------------|------------|
/// | 0     | 47:39         | 512       | Table/Block* | 512G       |
/// | 1     | 38:30         | 512       | Table/Block  | 1G         |
/// | 2     | 29:21         | 512       | Table/Block  | 2M         |
/// | 3     | 20:12         | 512       | Page         | 4K         |
///
/// *If effective value of TCR_ELx.DS is 0, level 0 allows Table descriptor only.
pub spec const VMSAV8_S1_ARCH: PTArch = PTArch(
    seq![
        PTArchLevel { num_entries: 512, frame_size: FrameSize::Size512G },
        PTArchLevel { num_entries: 512, frame_size: FrameSize::Size1G },
        PTArchLevel { num_entries: 512, frame_size: FrameSize::Size2M },
        PTArchLevel { num_entries: 512, frame_size: FrameSize::Size4K },
    ],
);

} // verus!
