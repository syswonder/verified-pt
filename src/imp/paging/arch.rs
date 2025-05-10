//! Defines VMSAv8-64 page table architecture, and provides architecture-specific utilities.
use crate::common::{
    addr::VAddrExec,
    arch::{PTArch, PTArchHelpers, PTArchLevel},
    frame::FrameSize,
};
use vstd::prelude::*;

verus! {

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

/// VMSAv8-64 4K page table architecture utilities.
pub struct VMSAv8_4kHelpers;

impl PTArchHelpers for VMSAv8_4kHelpers {
    open spec fn arch() -> PTArch {
        VMSAV8_4K_ARCH
    }

    fn frame_size(level: usize) -> (res: FrameSize) {
        if level == 0 {
            FrameSize::Size512G
        } else if level == 1 {
            FrameSize::Size1G
        } else if level == 2 {
            FrameSize::Size2M
        } else {
            FrameSize::Size4K
        }
    }

    fn pte_index(vaddr: VAddrExec, level: usize) -> (res: usize) {
        // Use division instead of bit shifts to avoid verus failure
        if level == 0 {
            vaddr.0 / 0x8000000000usize % 512
        } else if level == 1 {
            vaddr.0 / 0x40000000usize % 512
        } else if level == 2 {
            vaddr.0 / 0x200000usize % 512
        } else {
            vaddr.0 / 0x1000usize % 512
        }
    }
}

} // verus!
