//! Hardware specification.
//!
//！This module defines the abstract hardware state and the hardware behavior during memory
//！operations. The hardware state includes:
//！
//！- Physical memory.
//！- Page table memory.
//！- Translation Lookaside Buffer (TLB).
//！
//！The module specifies hardware behavior during memory translations, TLB management, and page
//！table operarations.
//！
//！**Assumption:** The hardware behavior refines the hardware specification, ensuring correctness
//！in memory translations. This specification underpins the entire verification process.
use vstd::prelude::*;

use crate::common::{
    addr::{VAddr, WORD_SIZE},
    frame::Frame,
    MemoryResult,
};
use super::memory::{PhysMem, PageTableMem, TLB};

verus! {

/// Abstract state managed by hardware.
pub struct HardwareState {
    /// Physical memory.
    pub mem: PhysMem,
    /// Page table.
    pub pt: PageTableMem,
    /// Translation Lookaside Buffer.
    pub tlb: TLB,
}

/// State transition specification.
impl HardwareState {
    /// Hardware init state.
    ///
    /// No mappings exist in the page table and TLB.
    pub open spec fn init(self) -> bool {
        &&& self.tlb.is_empty()
        &&& self.pt.interpret() === Map::empty()
    }

    /// Hardware state transition - memory read.
    pub open spec fn read(s1: Self, s2: Self, vaddr: VAddr, res: MemoryResult<u64>) -> bool {
        &&& vaddr.aligned(
            WORD_SIZE,
        )
        // Memory and page table should not be updated
        &&& s1.mem === s2.mem
        &&& s1.pt === s2.pt
        // Check mapping
        &&& if s1.tlb_has_mapping_for(vaddr) {
            // 1. TLB hit
            let (base, frame) = s1.tlb_mapping_for(vaddr);
            let pidx = vaddr.map(base, frame.base).idx();
            // Check frame attributes
            &&& if s1.mem.contains(pidx) && frame.attr.readable && frame.attr.user_accessible {
                &&& res is Ok
                &&& res->Ok_0 === s1.mem.read(pidx)
            } else {
                &&& res is PageFault
            }
            &&& s1.tlb === s2.tlb
        } else if s1.pt_has_mapping_for(vaddr) {
            // 2. TLB miss, page table hit
            let (base, frame) = s1.pt_mapping_for(vaddr);
            let pidx = vaddr.map(base, frame.base).idx();
            // Check frame attributes
            &&& if s1.mem.contains(pidx) && frame.attr.readable && frame.attr.user_accessible {
                &&& res is Ok
                &&& res->Ok_0 === s1.mem.read(pidx)
            } else {
                &&& res is PageFault
            }
            // TLB should be updated
            &&& s2.tlb === s1.tlb.update(base, frame)
        } else {
            // 3. TLB miss, page table miss
            &&& res is PageFault
            &&& s2.tlb === s1.tlb
        }
    }

    /// State transition - memory write.
    pub open spec fn write(
        s1: Self,
        s2: Self,
        vaddr: VAddr,
        value: u64,
        res: MemoryResult<()>,
    ) -> bool {
        &&& vaddr.aligned(WORD_SIZE)
        // Page table should not be updated
        &&& s1.pt === s2.pt
        // Check mapping
        &&& if s1.tlb_has_mapping_for(vaddr) {
            // 1. TLB hit
            let (base, frame) = s1.tlb_mapping_for(vaddr);
            let pidx = vaddr.map(base, frame.base).idx();
            // Check frame attributes
            &&& if s1.mem.contains(pidx) && frame.attr.writable && frame.attr.user_accessible {
                &&& res is Ok
                &&& s2.mem === s1.mem.write(pidx, value)
            } else {
                &&& res is PageFault
                &&& s2.mem === s1.mem
            }
            &&& s1.tlb === s2.tlb
        } else if s1.pt_has_mapping_for(vaddr) {
            // 2. TLB miss, page table hit
            let (base, frame) = s1.pt_mapping_for(vaddr);
            let pidx = vaddr.map(base, frame.base).idx();
            // Check frame attributes
            &&& if s1.mem.contains(pidx) && frame.attr.writable && frame.attr.user_accessible {
                &&& res is Ok
                &&& s2.mem === s1.mem.write(pidx, value)
            } else {
                &&& res is PageFault
                &&& s2.mem === s1.mem
            }
            // TLB should be updated
            &&& s2.tlb === s1.tlb.update(base, frame)
        } else {
            // 3. TLB miss, page table miss
            &&& res is PageFault
            &&& s2.mem === s1.mem
            &&& s2.tlb === s1.tlb
        }
    }

    /// State transition - Page table operation. This operation is performed when
    /// page table is accessed or modified by hypervisor.
    ///
    /// - Memory should not be updated.
    /// - New entries should not be added to TLB when operating the page table. They
    /// can only be added when TLB miss occurs during memory access.
    pub open spec fn pt_op(s1: Self, s2: Self) -> bool {
        &&& s1.mem === s2.mem
        &&& forall|vbase: VAddr, frame: Frame|
            s2.tlb.contains_mapping(vbase, frame) ==> s1.tlb.contains_mapping(vbase, frame)
    }

    /// State transition - explicit TLB eviction.
    pub open spec fn tlb_evict(s1: Self, s2: Self, vbase: VAddr) -> bool {
        &&& s1.tlb.contains_base(vbase)
        &&& s2.tlb === s1.tlb.evict(vbase)
        &&& s1.mem === s2.mem
        &&& s1.pt === s2.pt
    }
}

/// Helper functions.
impl HardwareState {
    /// If TLB has a mapping for `vaddr`.
    pub open spec fn tlb_has_mapping_for(self, vaddr: VAddr) -> bool {
        exists|vbase: VAddr, frame: Frame| #[trigger]
            self.tlb.contains_mapping(vbase, frame) && vaddr.within(vbase, frame.size.as_nat())
    }

    /// Get the mapping for `vaddr` in TLB.
    pub open spec fn tlb_mapping_for(self, vaddr: VAddr) -> (VAddr, Frame)
        recommends
            self.tlb_has_mapping_for(vaddr),
    {
        choose|vbase: VAddr, frame: Frame| #[trigger]
            self.tlb.contains_mapping(vbase, frame) && vaddr.within(vbase, frame.size.as_nat())
    }

    /// If page table has a mapping for `vaddr`.
    pub open spec fn pt_has_mapping_for(self, vaddr: VAddr) -> bool {
        exists|vbase: VAddr, frame: Frame| #[trigger]
            self.pt.interpret().contains_pair(vbase, frame) && vaddr.within(
                vbase,
                frame.size.as_nat(),
            )
    }

    /// Get the mapping for `vaddr` in page table.
    pub open spec fn pt_mapping_for(self, vaddr: VAddr) -> (VAddr, Frame)
        recommends
            self.pt_has_mapping_for(vaddr),
    {
        choose|vbase: VAddr, frame: Frame| #[trigger]
            self.pt.interpret().contains_pair(vbase, frame) && vaddr.within(
                vbase,
                frame.size.as_nat(),
            )
    }
}

} // verus!
