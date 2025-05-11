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
    addr::{PAddr, PIdx, VAddr, WORD_SIZE},
    arch::PTArch,
    frame::{Frame, FrameSize},
    MemoryResult,
};

verus! {

/// 8-byte-indexed physical memory.
pub struct PhysMem {
    /// Stored value
    pub mem: Seq<u64>,
    /// Start physical index
    pub base: PIdx,
}

impl PhysMem {
    /// Size of physical memory.
    pub open spec fn len(self) -> nat {
        self.mem.len()
    }

    /// Lower bound of physical memory.
    pub open spec fn lb(self) -> PIdx {
        self.base
    }

    /// Upper bound of physical memory
    pub open spec fn ub(self) -> PIdx {
        PIdx(self.base.0 + self.mem.len())
    }

    /// Read from physical memory.
    pub open spec fn read(self, pidx: PIdx) -> u64
        recommends
            self.lb().0 <= pidx.0 < self.ub().0,
    {
        self.mem[pidx.0 - self.base.0]
    }

    /// Write to physical memory.
    pub open spec fn write(self, pidx: PIdx, value: u64) -> Self
        recommends
            self.lb().0 <= pidx.0 < self.ub().0,
    {
        Self { mem: self.mem.update(pidx.0 - self.base.0, value), base: self.base }
    }

    /// If `pidx` is in the range of physical memory.
    pub open spec fn contains(self, pidx: PIdx) -> bool {
        self.lb().0 <= pidx.0 < self.ub().0
    }
}

/// Describe a page table stored in physical memory.
pub struct Table {
    /// Base address of the table.
    pub base: PAddr,
    /// Size of the table.
    pub size: FrameSize,
    /// Level of the table.
    pub level: nat,
}

/// Abstract model of page table memory, a memory region that stores page tables.
///
/// Hardware reads page table memory to perform page table walk, but cannot write to it.
/// Page table memory is modified by page table functions.
pub struct PageTableMem {
    /// All tables in the hierarchical page table, the first table is the root.
    pub tables: Seq<Table>,
    /// Page table architecture.
    pub arch: PTArch,
}

impl PageTableMem {
    /// Root page table address.
    pub open spec fn root(self) -> PAddr {
        self.tables[0].base
    }

    /// If the table with the given base address exists.
    pub open spec fn contains_table(self, base: PAddr) -> bool {
        exists|table: Table| #[trigger] self.tables.contains(table) && table.base == base
    }

    /// Get the table with the given base address.
    pub open spec fn table(self, base: PAddr) -> Table
        recommends
            self.contains_table(base),
    {
        choose|table: Table| #[trigger] self.tables.contains(table) && table.base == base
    }

    /// View a table as a sequence of entries.
    pub open spec fn table_view(self, base: PAddr) -> Seq<u64>
        recommends
            self.contains_table(base),
    ;

    /// Facts about table view.
    #[verifier::external_body]
    pub broadcast proof fn lemma_table_view(self, base: PAddr)
        requires
            self.invariants(),
        ensures
            #[trigger] self.table_view(base).len() == self.arch.entry_count(self.table(base).level),
    {
    }

    /// If accessing the given table at the given index is allowed.
    pub open spec fn accessible(self, base: PAddr, index: nat) -> bool {
        self.contains_table(base) && index < self.arch.entry_count(self.table(base).level)
    }

    /// Read the entry at the given index in the given table.
    pub open spec fn read(self, base: PAddr, index: nat) -> u64
        recommends
            self.accessible(base, index),
    {
        self.table_view(base)[index as int]
    }

    /// Interpret as `(vbase, frame)` mappings.
    ///
    /// This function extracts all mappings that valid hardware page table walks can reach.
    pub open spec fn interpret(self) -> Map<VAddr, Frame> {
        Map::new(
            |vaddr| exists|frame| #[trigger] self.walk(vaddr, frame),
            |vaddr| choose|frame| #[trigger] self.walk(vaddr, frame),
        )
    }

    /// Hardware page table walk behavior.
    ///
    /// Returns true for those vaddr and frame that valid hardware page table walks can reach.
    /// TODO: specify the behavior of hardware page table walk.
    pub open spec fn walk(self, vaddr: VAddr, frame: Frame) -> bool;

    /// Invariants.
    pub open spec fn invariants(self) -> bool {
        &&& self.arch.valid()
        // Root table is always present.
        &&& self.tables.len() > 0
        // Root table level is 0
        &&& self.tables[0].level == 0
        // Table level is valid.
        &&& forall|table: Table| #[trigger]
            self.tables.contains(table) ==> table.level
                < self.arch.level_count()
        // Table size is valid.
        &&& forall|i|
            0 <= i < self.tables.len() ==> #[trigger] self.tables[i].size.as_nat()
                == self.arch.table_size(
                self.tables[i].level,
            )
        // All tables should not overlap.
        &&& forall|i, j|
            0 <= i < self.tables.len() && 0 <= j < self.tables.len() ==> i == j || !PAddr::overlap(
                self.tables[i].base,
                self.tables[i].size.as_nat(),
                self.tables[j].base,
                self.tables[j].size.as_nat(),
            )
    }

    /// Init State.
    pub open spec fn init(self) -> bool {
        &&& self.arch.valid()
        &&& self.tables.len() == 1
        &&& self.tables[0].size.as_nat() == self.arch.table_size(0)
        &&& self.table_view(self.root()) == seq![0u64; self.arch.entry_count(0)]
    }

    /// Alloc a new table.
    pub open spec fn alloc_table(s1: Self, s2: Self, level: nat, table: Table) -> bool {
        &&& s2.arch == s1.arch
        // `s1` doesn't have the table
        &&& !s1.tables.contains(table)
        // new table has valid level
        &&& table.level == level
        &&& 0 < level < s1.arch.level_count()
        // new table has valid size
        &&& table.size.as_nat() == s1.arch.table_size(
            level,
        )
        // new table is aligned
        &&& table.base.aligned(table.size.as_nat())
        // new table is empty
        &&& s2.table_view(table.base)
            == seq![0u64; s1.arch.entry_count(level)]
        // new table doesn't overlap with existing tables
        &&& forall|i|
            #![auto]
            0 <= i < s1.tables.len() ==> !PAddr::overlap(
                s1.tables[i].base,
                s1.tables[i].size.as_nat(),
                table.base,
                table.size.as_nat(),
            )
            // `tables` is updated
        &&& s2.tables == s1.tables.push(table)
    }

    /// Write the entry at the given index in the given table.
    pub open spec fn write(s1: Self, s2: Self, base: PAddr, index: nat, entry: u64) -> bool {
        &&& s2.arch == s1.arch
        // Tables are the same
        &&& s2.tables == s1.tables
        // The entry is accessible
        &&& s1.accessible(base, index)
        // The entry is updated
        &&& s2.table_view(base) == s1.table_view(base).update(index as int, entry)
    }

    /// Lemma. Always contains a root table.
    pub proof fn lemma_contains_root(self)
        requires
            self.invariants(),
        ensures
            self.contains_table(self.root()),
            self.table(self.root()) == self.tables[0],
    {
        assert(self.tables.contains(self.tables[0]));
        self.lemma_table_base_unique();
    }

    /// Lemma. If table exists, and the index used to access table is acquired by `pte_index`,
    /// then the entry is accessible.
    pub proof fn lemma_accessible(self, base: PAddr, vaddr: VAddr, level: nat)
        requires
            self.invariants(),
            self.contains_table(base),
            self.table(base).level == level,
            level < self.arch.level_count(),
        ensures
            self.accessible(base, self.arch.pte_index(vaddr, level)),
    {
    }

    /// Lemma. Different tables have different base addresses.
    pub proof fn lemma_table_base_unique(self)
        requires
            self.invariants(),
        ensures
            forall|i, j|
                #![auto]
                0 <= i < self.tables.len() && 0 <= j < self.tables.len() ==> i == j
                    || self.tables[i].base != self.tables[j].base,
    {
        assert forall|i, j|
            #![auto]
            0 <= i < self.tables.len() && 0 <= j < self.tables.len() implies i == j
            || self.tables[i].base != self.tables[j].base by {
            if i != j && self.tables[i].base == self.tables[j].base {
                assert(PAddr::overlap(
                    self.tables[i].base,
                    self.tables[i].size.as_nat(),
                    self.tables[j].base,
                    self.tables[j].size.as_nat(),
                ));
            }
        }
    }

    /// Lemma. `alloc_table` preserves invariants.
    pub proof fn lemma_alloc_table_preserves_invariants(
        s1: Self,
        s2: Self,
        level: nat,
        table: Table,
    )
        requires
            s1.invariants(),
            Self::alloc_table(s1, s2, level, table),
        ensures
            s2.invariants(),
    {
        assert forall|table2: Table| #[trigger] s2.tables.contains(table2) implies table2.level
            < s2.arch.level_count() by {
            if table2 != table {
                assert(s1.tables.contains(table2));
            }
        }
    }

    /// Lemma. `write` preserves invariants.
    pub proof fn lemma_write_preserves_invariants(
        s1: Self,
        s2: Self,
        base: PAddr,
        index: nat,
        entry: u64,
    )
        requires
            s1.invariants(),
            Self::write(s1, s2, base, index, entry),
        ensures
            s2.invariants(),
    {
    }
}

/// Translation Lookaside Buffer (TLB).
pub struct TLB(pub Map<VAddr, Frame>);

/// TLB specification.
impl TLB {
    /// Is empty.
    pub open spec fn is_empty(self) -> bool {
        self.0 === Map::empty()
    }

    /// Fill a TLB entry.
    pub open spec fn fill(self, vbase: VAddr, frame: Frame) -> Self
        recommends
            !self.0.contains_key(vbase),
    {
        TLB(self.0.insert(vbase, frame))
    }

    /// Evict a TLB entry.
    pub open spec fn evict(self, vbase: VAddr) -> Self
        recommends
            self.0.contains_key(vbase),
    {
        TLB(self.0.remove(vbase))
    }

    /// If TLB has a mapping with given base.
    pub open spec fn contains_base(self, vbase: VAddr) -> bool {
        self.0.contains_key(vbase)
    }

    /// If TLB has a given mapping `(base, frame)`
    pub open spec fn contains_mapping(self, vbase: VAddr, frame: Frame) -> bool {
        self.0.contains_pair(vbase, frame)
    }

    /// Index a TLB entry.
    pub open spec fn index(self, vbase: VAddr) -> Frame
        recommends
            self.contains_base(vbase),
    {
        self.0[vbase]
    }

    /// Check if a new entry conflicts with an existing TLB entry, return the conflicting entry.
    ///
    /// The concrete strategy varies depending on the TLB implementation.
    /// This specification does not dictate the eviction strategy.
    pub open spec fn conflict(self, vbase: VAddr, frame: Frame) -> Option<VAddr>;

    /// The conflict entry returned by `conflict` must be in the TLB.
    ///
    /// This is an assumption made about the concrete TLB behavior.
    #[verifier::external_body]
    pub broadcast proof fn lemma_conflict(self, vbase: VAddr, frame: Frame)
        ensures
            match #[trigger] self.conflict(vbase, frame) {
                Some(conflict) => self.0.contains_key(conflict),
                None => !self.0.contains_key(vbase),
            },
    {
    }

    /// Update TLB with a new entry, if there is a conflict, evict the conflicting entry.
    pub open spec fn update(self, vbase: VAddr, frame: Frame) -> Self
        recommends
            !self.0.contains_key(vbase),
    {
        if let Some(conflict) = self.conflict(vbase, frame) {
            self.evict(conflict).fill(vbase, frame)
        } else {
            self.fill(vbase, frame)
        }
    }
}

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
