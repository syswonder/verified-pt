//! Hardware-level memory state transition specification.
//!
//! The hardware-level state transition is specified by several operations. The actual hardware’s
//! behavior must be a refinement of this specification.
//!
//! Hardware state transition step includes:
//!
//! - Memory read & write
//! - Page table memory operation
//! - TLB fill & evict.
use vstd::prelude::*;

use super::mem::{Frame, ReadOp, WriteOp};
use super::os::OSMemoryState;
use super::{PAddr, VAddr};

verus! {

impl OSMemoryState {
    /// State transition - Common memory read operation.
    ///
    /// The pre-state `s1` and post-state `s2` must satisfy the specification
    /// after common memory read operation.
    pub open spec fn hw_mem_read(
        s1: Self,
        s2: Self,
        op: ReadOp,
        paddr: PAddr,
        mapping: Option<(VAddr, Frame)>,
    ) -> bool {
        // Memory should not be updated
        &&& s1.mem === s2.mem
        // Check mapping
        &&& match mapping {
            Some((base, frame)) => {
                // If `mapping` is `Some`,
                &&& s1.exists_mapping_for(
                    op.vaddr,
                )
                // `vaddr` should be in the virtual page mapped by `base`
                &&& op.vaddr.within(
                    base,
                    frame.size.as_nat(),
                )
                // `vaddr` should map to `paddr`
                &&& op.vaddr.map(base, frame.base)
                    === paddr
                // Check frame attributes
                &&& if !frame.attr.readable || !frame.attr.user_accessible {
                    // If the frame is not readable or user accessible, the
                    // result should be `Err`
                    op.result is Err
                } else {
                    // Otherwise, the result should be `Ok`
                    &&& op.result is Ok
                    &&& op.result.unwrap() === s1.mem[op.vaddr.map(
                        base,
                        frame.base,
                    ).word_idx().as_int()]
                }
            },
            None => {
                // If `mapping` is `None`
                &&& !s1.exists_mapping_for(
                    op.vaddr,
                )
                // Result should be `Err`
                &&& op.result is Err
            },
        }
    }

    /// State transition - Common memory write operation.
    ///
    /// The pre-state `s1` and post-state `s2` must satisfy the specification
    /// after common memory write operation.
    pub open spec fn hw_mem_write(
        s1: Self,
        s2: Self,
        op: WriteOp,
        paddr: PAddr,
        mapping: Option<(VAddr, Frame)>,
    ) -> bool {
        // Check mapping
        &&& match mapping {
            Some((base, frame)) => {
                // If `mapping` is `Some`,
                &&& s1.exists_mapping_for(
                    op.vaddr,
                )
                // `vaddr` should be in the virtual page mapped by `base`
                &&& op.vaddr.within(
                    base,
                    frame.size.as_nat(),
                )
                // `vaddr` should map to `paddr`
                &&& op.vaddr.map(base, frame.base)
                    === paddr
                // Check frame attributes
                &&& if !frame.attr.writable || !frame.attr.user_accessible {
                    // If the frame is not writable or user accessible, the
                    // result should be `Err`
                    &&& op.result is Err
                    // Memory should not be updated
                    &&& s1.mem === s2.mem
                } else {
                    // Otherwise, the result should be `Ok`
                    &&& op.result is Ok
                    &&& s2.mem === s1.mem.update(
                        op.vaddr.map(base, frame.base).word_idx().as_int(),
                        op.value,
                    )
                }
            },
            None => {
                // If `mapping` is `None`
                &&& !s1.exists_mapping_for(
                    op.vaddr,
                )
                // Result should be `Err`
                &&& op.result is Err
                // Memory should not be updated
                &&& s1.mem === s2.mem
            },
        }
    }

    /// State transition - Page table memory operation.
    ///
    /// The pre-state `s1` and post-state `s2` must satisfy the specification
    /// after page table memory operation.
    pub open spec fn hw_pt_mem_op(s1: Self, s2: Self) -> bool {
        // Memory should not be updated
        &&& s1.mem === s2.mem
    }

    /// State transition - TLB fill operation.
    ///
    /// The pre-state `s1` and post-state `s2` must satisfy the specification
    /// after TLB fill operation.
    pub open spec fn hw_tlb_fill(s1: Self, s2: Self, vaddr: VAddr, frame: Frame) -> bool {
        // Page table must contain the mapping
        &&& s1.interpret_pt_mem().contains_pair(
            vaddr,
            frame,
        )
        // Insert into tlb
        &&& s2.tlb === s1.tlb.insert(
            vaddr,
            frame,
        )
        // Memory and page table should not be updated
        &&& s1.mem === s2.mem
        &&& s1.pt_mem === s2.pt_mem
    }

    /// State transition - TLB eviction operation.
    ///
    /// The pre-state `s1` and post-state `s2` must satisfy the specification
    /// after TLB eviction operation.
    pub open spec fn hw_tlb_evict(s1: Self, s2: Self, vaddr: VAddr) -> bool {
        // TLB must contain the mapping
        &&& s1.tlb.contains_key(vaddr)
        // Remove from tlb
        &&& s2.tlb === s1.tlb.remove(
            vaddr,
        )
        // Memory and page table should not be updated
        &&& s1.mem === s2.mem
        &&& s1.pt_mem === s2.pt_mem
    }
}

} // verus!
