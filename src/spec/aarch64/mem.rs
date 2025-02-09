//! Defination of memory management structures and functions.
use vstd::prelude::*;

verus! {

/// Page & Block size supported by VMSA-v8.
pub enum FrameSize {
    /// 4 KiB
    Size4K,
    /// 64 KiB
    Size64K,
    /// 1 GiB
    Size1G,
}

impl FrameSize {
    pub open spec fn as_u64(self) -> u64 {
        match self {
            FrameSize::Size4K => 4096,
            FrameSize::Size64K => 65536,
            FrameSize::Size1G => 1073741824,
        }
    }
}

/// Frame attributes specification. Defination consistent with `hvisor::memory::MemFlags`.
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
    pub base: u64,
    /// The size of the frame in bytes.
    pub size: FrameSize,
    /// The attributes of the frame.
    pub attr: FrameAttr,
}

pub struct PageTableMem {}

impl PageTableMem {
    pub fn new() -> Self {
        Self {  }
    }

    pub open spec fn root(self) -> u64 {
        0
    }

    pub open spec fn read(&self, addr: u64) -> u64 {
        // TODO: read from memory
        0
    }

    pub fn write(&self, addr: u64, data: u64) {
        // TODO: write to memory
    }
}

} // verus!
