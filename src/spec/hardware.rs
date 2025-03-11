//! Hardware specification.
//!
//! This module defines the abstract hardware state and its transition behaviors for memory
//! management. The hardware state includes physical memory, a page table, and a Translation
//! Lookaside Buffer (TLB). The module specifies how the hardware behaves during memory
//! operations, TLB management, and page table updates.
//!
//! Assumption. The hardware behavior refines the hardware specification, ensuring correctness
//! in memory translations. The hardware specification serves as the foundation for verifying
//! the correctness of the memory management system.
use vstd::prelude::*;

use super::{
    addr::{VAddr, WORD_SIZE},
    frame::Frame,
    op::{ReadOp, TLBEvictOp, TLBFillOp, WriteOp},
    s1pt::S1PageTable,
};

verus! {

/// Abstract state managed by hardware.
pub struct HardwareState {
    /// 8-byte-indexed physical memory.
    pub mem: Seq<nat>,
    /// Page table.
    pub pt: S1PageTable,
    /// Translation Lookaside Buffer.
    pub tlb: Map<VAddr, Frame>,
}

impl HardwareState {
    /// Hardware init state.
    pub open spec fn hw_init(self) -> bool {
        &&& self.tlb === Map::empty()
        &&& self.pt.interpret() === Map::empty()
    }

    /// Hardware state transition - memory read.
    pub open spec fn hw_read(s1: Self, s2: Self, op: ReadOp) -> bool {
        &&& op.vaddr.aligned(
            WORD_SIZE,
        )
        // Memory, page table and TLB should not be updated
        &&& s1.mem === s2.mem
        &&& s1.pt === s2.pt
        &&& s1.tlb === s2.tlb
        // Check mapping
        &&& match op.mapping {
            Some((base, frame)) => {
                // If `mapping` is `Some`, it should be cached by TLB
                &&& s1.tlb.contains_pair(
                    base,
                    frame,
                )
                // `vaddr` should be in the virtual page mapped by `base`
                &&& op.vaddr.within(
                    base,
                    frame.size.as_nat(),
                )
                // `vaddr` should map to `paddr`
                &&& op.vaddr.map(base, frame.base)
                    === op.paddr
                // Check frame attributes
                &&& if op.vaddr.map(base, frame.base).idx().0 < s1.mem.len() && frame.attr.readable
                    && frame.attr.user_accessible {
                    // The result should be `Ok`
                    &&& op.result is Ok
                    &&& op.result.unwrap() === s1.mem[op.vaddr.map(base, frame.base).idx().as_int()]
                } else {
                    // The result should be `Err`
                    op.result is Err
                }
            },
            None => {
                // If `mapping` is `None`
                &&& !s1.has_mapping_for(
                    op.vaddr,
                )
                // Result should be `Err`
                &&& op.result is Err
            },
        }
    }

    /// State transition - memory write.
    pub open spec fn hw_write(s1: Self, s2: Self, op: WriteOp) -> bool {
        &&& op.vaddr.aligned(
            WORD_SIZE,
        )
        // Page table and TLB should not be updated
        &&& s1.pt === s2.pt
        &&& s1.tlb === s2.tlb
        // Check mapping
        &&& match op.mapping {
            Some((base, frame)) => {
                // If `mapping` is `Some`, it should be cached by TLB
                &&& s1.tlb.contains_pair(
                    base,
                    frame,
                )
                // `vaddr` should be in the virtual page mapped by `base`
                &&& op.vaddr.within(
                    base,
                    frame.size.as_nat(),
                )
                // `vaddr` should map to `paddr`
                &&& op.vaddr.map(base, frame.base)
                    === op.paddr
                // Check frame attributes
                &&& if op.vaddr.map(base, frame.base).idx().0 < s1.mem.len() && frame.attr.writable
                    && frame.attr.user_accessible {
                    // The result should be `Ok`
                    &&& op.result is Ok
                    // Update memory
                    &&& s2.mem === s1.mem.update(
                        op.vaddr.map(base, frame.base).idx().as_int(),
                        op.value,
                    )
                } else {
                    // The result should be `Err`
                    &&& op.result is Err
                    // Memory should not be updated
                    &&& s1.mem === s2.mem
                }
            },
            None => {
                // If `mapping` is `None`
                &&& !s1.has_mapping_for(
                    op.vaddr,
                )
                // Result should be `Err`
                &&& op.result is Err
                // Memory should not be updated
                &&& s1.mem === s2.mem
            },
        }
    }

    /// State transition - Page table operation.
    pub open spec fn hw_pt_op(s1: Self, s2: Self) -> bool {
        // Memory should not be updated
        &&& s1.mem
            === s2.mem
        // After page table update, hardware should ensure s2.tlb is a submap of s1.tlb
        &&& forall|base: VAddr, frame: Frame|
            s2.tlb.contains_pair(base, frame) ==> s1.tlb.contains_pair(base, frame)
    }

    /// State transition - TLB fill.
    pub open spec fn hw_tlb_fill(s1: Self, s2: Self, op: TLBFillOp) -> bool {
        // Page table must contain the mapping
        &&& s1.pt.interpret().contains_pair(
            op.vaddr,
            op.frame,
        )
        // Insert into tlb
        &&& s2.tlb === s1.tlb.insert(
            op.vaddr,
            op.frame,
        )
        // Memory and page table should not be updated
        &&& s1.mem === s2.mem
        &&& s1.pt === s2.pt
    }

    /// State transition - TLB eviction.
    pub open spec fn hw_tlb_evict(s1: Self, s2: Self, op: TLBEvictOp) -> bool {
        // TLB must contain the mapping
        &&& s1.tlb.contains_key(op.vaddr)
        // Remove from tlb
        &&& s2.tlb === s1.tlb.remove(
            op.vaddr,
        )
        // Memory and page table should not be updated
        &&& s1.mem === s2.mem
        &&& s1.pt === s2.pt
    }

    /// If exists a mapping that `vaddr` lies in.
    pub open spec fn has_mapping_for(self, vaddr: VAddr) -> bool {
        exists|base: VAddr, frame: Frame| #[trigger]
            self.pt.interpret().contains_pair(base, frame) && vaddr.within(
                base,
                frame.size.as_nat(),
            )
    }
}

} // verus!
