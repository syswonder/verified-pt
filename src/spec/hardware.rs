//! Hardware specification.
//!
//！This module defines the abstract hardware state and its transition behaviors during memory
//！operations. The hardware state includes:
//！
//！- **Physical memory**
//！- **Page table**
//！- **Translation Lookaside Buffer (TLB)**
//！
//！The module specifies hardware behavior during memory translations, TLB management, and page
//！table updates.
//！
//！**Assumption:** The hardware behavior refines the hardware specification, ensuring correctness
//！in memory translations. This specification underpins the entire verification process.
use vstd::prelude::*;

use super::{
    addr::{VAddr, WORD_SIZE},
    frame::Frame,
    s1pt::S1PageTable,
};

verus! {

/// Translation Lookaside Buffer (TLB).
pub struct TLB(pub Map<VAddr, Frame>);

/// TLB specification.
impl TLB {
    /// Is empty.
    pub open spec fn is_empty(self) -> bool {
        self.0 === Map::empty()
    }

    /// Fill a TLB entry.
    pub open spec fn fill(self, base: VAddr, frame: Frame) -> Self
        recommends
            !self.0.contains_key(base),
    {
        TLB(self.0.insert(base, frame))
    }

    /// Evict a TLB entry.
    pub open spec fn evict(self, base: VAddr) -> Self
        recommends
            self.0.contains_key(base),
    {
        TLB(self.0.remove(base))
    }

    /// If TLB has a mapping with given base.
    pub open spec fn contains_base(self, base: VAddr) -> bool {
        self.0.contains_key(base)
    }

    /// If TLB has a given mapping `(base, frame)`
    pub open spec fn contains_mapping(self, base: VAddr, frame: Frame) -> bool {
        self.0.contains_pair(base, frame)
    }

    /// Index a TLB entry.
    pub open spec fn index(self, base: VAddr) -> Frame
        recommends
            self.contains_base(base),
    {
        self.0[base]
    }

    /// Check if a new entry conflicts with an existing TLB entry, return the conflicting entry.
    ///
    /// The concrete strategy varies depending on the TLB implementation.
    /// This specification does not dictate the eviction strategy.
    pub open spec fn has_conflict(self, base: VAddr, frame: Frame) -> Option<VAddr>;

    /// The conflict entry returned by `has_conflict` is in the TLB.
    #[verifier::external_body]
    pub broadcast proof fn lemma_has_conflict(self, base: VAddr, frame: Frame)
        ensures
            match #[trigger] self.has_conflict(base, frame) {
                Some(conflict) => self.0.contains_key(conflict),
                None => !self.0.contains_key(base),
            },
    {
    }

    /// Update TLB with a new entry, if there is a conflict, evict the conflicting entry.
    pub open spec fn update(self, base: VAddr, frame: Frame) -> Self
        recommends
            !self.0.contains_key(base),
    {
        if let Some(conflict) = self.has_conflict(base, frame) {
            self.evict(conflict).fill(base, frame)
        } else {
            self.fill(base, frame)
        }
    }
}

/// Abstract state managed by hardware.
pub struct HardwareState {
    /// 8-byte-indexed physical memory.
    pub mem: Seq<u64>,
    /// Page table.
    pub pt: S1PageTable,
    /// Translation Lookaside Buffer.
    pub tlb: TLB,
}

/// State transition specification.
impl HardwareState {
    /// Hardware init state.
    pub open spec fn init(self) -> bool {
        &&& self.tlb.is_empty()
        &&& self.pt.interpret() === Map::empty()
    }

    /// Hardware state transition - memory read.
    pub open spec fn read(s1: Self, s2: Self, vaddr: VAddr, res: Result<u64, ()>) -> bool {
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
            // Check frame attributes
            &&& if vaddr.map(base, frame.base).idx().0 < s1.mem.len() && frame.attr.readable
                && frame.attr.user_accessible {
                &&& res is Ok
                &&& res.unwrap() === s1.mem[vaddr.map(base, frame.base).idx().as_int()]
            } else {
                &&& res is Err
            }
            &&& s1.tlb === s2.tlb
        } else if s1.pt_has_mapping_for(vaddr) {
            // 2. TLB miss, page table hit
            let (base, frame) = s1.pt_mapping_for(vaddr);
            // Check frame attributes
            &&& if vaddr.map(base, frame.base).idx().0 < s1.mem.len() && frame.attr.readable
                && frame.attr.user_accessible {
                &&& res is Ok
                &&& res.unwrap() === s1.mem[vaddr.map(base, frame.base).idx().as_int()]
            } else {
                &&& res is Err
            }
            // TLB should be updated
            &&& s2.tlb === s1.tlb.update(base, frame)
        } else {
            // 3. TLB miss, page table miss
            &&& res is Err
            &&& s2.tlb === s1.tlb
        }
    }

    /// State transition - memory write.
    pub open spec fn write(
        s1: Self,
        s2: Self,
        vaddr: VAddr,
        value: u64,
        res: Result<(), ()>,
    ) -> bool {
        &&& vaddr.aligned(WORD_SIZE)
        // Page table should not be updated
        &&& s1.pt === s2.pt
        // Check mapping
        &&& if s1.tlb_has_mapping_for(vaddr) {
            // 1. TLB hit
            let (base, frame) = s1.tlb_mapping_for(vaddr);
            // Check frame attributes
            &&& if vaddr.map(base, frame.base).idx().0 < s1.mem.len() && frame.attr.writable
                && frame.attr.user_accessible {
                &&& res is Ok
                &&& s2.mem === s1.mem.update(vaddr.map(base, frame.base).idx().as_int(), value)
            } else {
                &&& res is Err
                &&& s2.mem === s1.mem
            }
            &&& s1.tlb === s2.tlb
        } else if s1.pt_has_mapping_for(vaddr) {
            // 2. TLB miss, page table hit
            let (base, frame) = s1.pt_mapping_for(vaddr);
            // Check frame attributes
            &&& if vaddr.map(base, frame.base).idx().0 < s1.mem.len() && frame.attr.writable
                && frame.attr.user_accessible {
                &&& res is Ok
                &&& s2.mem === s1.mem.update(vaddr.map(base, frame.base).idx().as_int(), value)
            } else {
                &&& res is Err
                &&& s2.mem === s1.mem
            }
            // TLB should be updated
            &&& s2.tlb === s1.tlb.update(base, frame)
        } else {
            // 3. TLB miss, page table miss
            &&& res is Err
            &&& s2.mem === s1.mem
            &&& s2.tlb === s1.tlb
        }
    }

    /// State transition - Page table operation. This operation is performed when
    /// page table is operated by hypervisor.
    ///
    /// - Memory should not be updated.
    /// - New entries should not be added to TLB when operating the page table. They
    /// can only be added when TLB miss occurs during memory access.
    pub open spec fn pt_op(s1: Self, s2: Self) -> bool {
        &&& s1.mem === s2.mem
        &&& forall|base: VAddr, frame: Frame|
            s2.tlb.contains_mapping(base, frame) ==> s1.tlb.contains_mapping(base, frame)
    }

    /// State transition - explicit TLB eviction.
    pub open spec fn tlb_evict(s1: Self, s2: Self, base: VAddr) -> bool {
        &&& s1.tlb.contains_base(base)
        &&& s2.tlb === s1.tlb.evict(base)
        &&& s1.mem === s2.mem
        &&& s1.pt === s2.pt
    }
}

/// Helper functions.
impl HardwareState {
    /// If TLB has a mapping for `vaddr`.
    pub open spec fn tlb_has_mapping_for(self, vaddr: VAddr) -> bool {
        exists|base: VAddr, frame: Frame| #[trigger]
            self.tlb.contains_mapping(base, frame) && vaddr.within(base, frame.size.as_nat())
    }

    /// Get the mapping for `vaddr` in TLB.
    pub open spec fn tlb_mapping_for(self, vaddr: VAddr) -> (VAddr, Frame)
        recommends
            self.tlb_has_mapping_for(vaddr),
    {
        choose|base: VAddr, frame: Frame| #[trigger]
            self.tlb.contains_mapping(base, frame) && vaddr.within(base, frame.size.as_nat())
    }

    /// If page table has a mapping for `vaddr`.
    pub open spec fn pt_has_mapping_for(self, vaddr: VAddr) -> bool {
        exists|base: VAddr, frame: Frame| #[trigger]
            self.pt.interpret().contains_pair(base, frame) && vaddr.within(
                base,
                frame.size.as_nat(),
            )
    }

    /// Get the mapping for `vaddr` in page table.
    pub open spec fn pt_mapping_for(self, vaddr: VAddr) -> (VAddr, Frame)
        recommends
            self.pt_has_mapping_for(vaddr),
    {
        choose|base: VAddr, frame: Frame| #[trigger]
            self.pt.interpret().contains_pair(base, frame) && vaddr.within(
                base,
                frame.size.as_nat(),
            )
    }
}

} // verus!
