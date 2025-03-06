//! High-level & OS-level state machine operations.
use vstd::prelude::*;

use super::addr::{PAddr, VAddr};
use super::mem::Frame;

verus! {

/// Memory read operation and result.
pub struct ReadOp {
    /// Virtual address.
    pub vaddr: VAddr,
    /// Physical address.
    pub paddr: PAddr,
    /// Involved page mapping.
    pub mapping: Option<(VAddr, Frame)>,
    /// Read result.
    pub result: Result<nat, ()>,
}

/// Memory write operation and result.
pub struct WriteOp {
    /// Virtual address.
    pub vaddr: VAddr,
    /// Physical address.
    pub paddr: PAddr,
    /// Value to write.
    pub value: nat,
    /// Involved page mapping.
    pub mapping: Option<(VAddr, Frame)>,
    /// Write result.
    pub result: Result<(), ()>,
}

/// Virtual page map operation and result.
pub struct MapOp {
    /// Virtual page base address.
    pub vaddr: VAddr,
    /// Frame to map.
    pub frame: Frame,
    /// Mapping result.
    pub result: Result<(), ()>,
}

/// Virtual page unmap operation and result.
pub struct UnmapOp {
    /// Virtual page base address.
    pub vaddr: VAddr,
    /// Unmapping result.
    pub result: Result<(), ()>,
}

/// Page table query operation and result.
pub struct QueryOp {
    /// Virtual page address.
    pub vaddr: VAddr,
    /// Query result.
    pub result: Result<(VAddr, Frame), ()>,
}

/// TLB fill operation.
pub struct TLBFillOp {
    /// Virtual page address.
    pub vaddr: VAddr,
    /// Frame to map.
    pub frame: Frame,
}

/// TLB eviction operation.
pub struct TLBEvictOp {
    /// Virtual page address.
    pub vaddr: VAddr,
}

} // verus!
