//! Memory related structs and functions.
use vstd::prelude::*;

use super::addr::{PAddr, PAddrExec};

verus! {

/// Page & Block size supported by VMSA-v8.
pub enum FrameSize {
    /// 4 KiB
    Size4K,
    /// 2 MiB
    Size2M,
    /// 1 GiB
    Size1G,
}

impl FrameSize {
    /// Convert to usize.
    pub open spec fn as_usize(self) -> usize {
        match self {
            FrameSize::Size4K => 0x1000,
            FrameSize::Size2M => 0x200000,
            FrameSize::Size1G => 0x40000000,
        }
    }

    /// Convert to nat.
    pub open spec fn as_nat(self) -> nat {
        self.as_usize() as nat
    }
}

/// Frame attributes. Defination consistent with `hvisor::memory::MemFlags`.
#[derive(PartialEq, Eq)]
pub struct FrameAttr {
    /// Whether the memory is readable.
    pub readable: bool,
    /// Whether the memory is writable.
    pub writable: bool,
    /// Whether the memory is executable.
    pub executable: bool,
    /// Whether the memory is user accessible.
    pub user_accessible: bool,
}

/// Represents a physical memory frame (Page or Block).
pub struct Frame {
    /// The base address of the frame.
    pub base: PAddr,
    /// The size of the frame in bytes.
    pub size: FrameSize,
    /// The attributes of the frame.
    pub attr: FrameAttr,
}

/// (EXEC-MODE) represents a physical memory frame (Page or Block).
pub struct FrameExec {
    /// The base address of the frame.
    pub base: PAddrExec,
    /// The size of the frame in bytes.
    pub size: FrameSize,
    /// The attributes of the frame.
    pub attr: FrameAttr,
}

impl FrameExec {
    /// Convert to Frame.
    pub open spec fn view(self) -> Frame {
        Frame { base: self.base@, size: self.size, attr: self.attr }
    }
}

} // verus!
