/// Model of physical memory, page table memory, and TLB.
use vstd::prelude::*;

use crate::common::{
    addr::{PAddr, PAddrExec, PIdx, VAddr},
    arch::{PTArch, PTArchExec},
    frame::{Frame, FrameSize},
};

verus! {

/// 8-byte-indexed physical memory model.
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

/// Translation lookaside buffer (TLB) model.
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
    pub broadcast proof fn table_view_facts(self, base: PAddr)
        requires
            self.invariants(),
        ensures
            #[trigger] self.table_view(base).len() == self.arch.entry_count(self.table(base).level),
    {
    }

    /// If a table is empty.
    pub open spec fn is_table_empty(self, base: PAddr) -> bool
        recommends
            self.contains_table(base),
    {
        self.table_view(base) == seq![0u64; self.table_view(base).len()]
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
        &&& forall|i|
            0 <= i < self.tables.len() ==> #[trigger] self.tables[i].level
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
        &&& self.tables[0].level == 0
        &&& self.tables[0].size.as_nat() == self.arch.table_size(0)
        &&& self.table_view(self.root()) == seq![0u64; self.arch.entry_count(0)]
    }

    /// Allocate a new table.
    pub open spec fn alloc_table(self, level: nat) -> (Self, Table)
        recommends
            self.invariants(),
            level < self.arch.level_count(),
    ;

    /// Facts that `alloc_table` should satisfy.
    #[verifier::external_body]
    pub broadcast proof fn alloc_table_facts(self, level: nat)
        requires
            self.invariants(),
            level < self.arch.level_count(),
        ensures
            ({
                let (s2, table) = #[trigger] self.alloc_table(level);
                &&& s2.arch == self.arch
                // `self` doesn't have the table
                &&& !self.contains_table(
                    table.base,
                )
                // new table has valid level
                &&& table.level == level
                // new table has valid size
                &&& table.size.as_nat() == self.arch.table_size(
                    level,
                )
                // new table is aligned
                &&& table.base.aligned(
                    table.size.as_nat(),
                )
                // new table is empty
                &&& s2.table_view(table.base)
                    == seq![0u64; self.arch.entry_count(level)]
                // old tables are the same
                &&& forall|base: PAddr| #[trigger]
                    self.contains_table(base) ==> s2.table_view(base) == self.table_view(
                        base,
                    )
                // new table doesn't overlap with existing tables
                &&& forall|i|
                    #![auto]
                    0 <= i < self.tables.len() ==> !PAddr::overlap(
                        self.tables[i].base,
                        self.tables[i].size.as_nat(),
                        table.base,
                        table.size.as_nat(),
                    )
                    // `tables` is updated
                &&& s2.tables == self.tables.push(table)
            }),
    {
    }

    /// Deallocate a table.
    pub open spec fn dealloc_table(self, base: PAddr) -> Self
        recommends
            self.invariants(),
            self.contains_table(base),
            base != self.root(),
    {
        let i = choose|i| 0 <= i < self.tables.len() && #[trigger] self.tables[i].base == base;
        Self { arch: self.arch, tables: self.tables.remove(i) }
    }

    /// Update the entry at the given index in the given table.
    pub open spec fn write(self, base: PAddr, index: nat, entry: u64) -> Self;

    /// Facts that `write` should satisfy.
    #[verifier::external_body]
    pub broadcast proof fn write_facts(self, base: PAddr, index: nat, entry: u64)
        requires
            self.invariants(),
            self.accessible(base, index),
        ensures
            ({
                let s2 = #[trigger] self.write(base, index, entry);
                &&& s2.arch == self.arch
                // Tables are the same
                &&& s2.tables == self.tables
                // The entry is updated
                &&& s2.table_view(base) == self.table_view(base).update(
                    index as int,
                    entry,
                )
                // Other tables contents are the same
                &&& forall|i|
                    #![auto]
                    0 <= i < self.tables.len() && self.tables[i].base != base ==> s2.table_view(
                        self.tables[i].base,
                    ) == self.table_view(self.tables[i].base)
            }),
    {
    }

    /// Lemma. Different tables have different base addresses.
    pub broadcast proof fn lemma_table_base_unique(self)
        requires
            #[trigger] self.invariants(),
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

    /// Lemma. Always contains a root table.
    pub broadcast proof fn lemma_contains_root(self)
        requires
            #[trigger] self.invariants(),
        ensures
            self.contains_table(self.root()),
            self.table(self.root()) == self.tables[0],
    {
        assert(self.tables.contains(self.tables[0]));
        self.lemma_table_base_unique();
    }

    /// Lemma. `init` implies invariants.
    pub broadcast proof fn lemma_init_implies_invariants(self)
        requires
            #[trigger] self.init(),
        ensures
            self.invariants(),
    {
    }

    /// Lemma. `alloc_table` preserves invariants.
    pub broadcast proof fn lemma_alloc_table_preserves_invariants(self, level: nat)
        requires
            self.invariants(),
            level < self.arch.level_count(),
        ensures
            #[trigger] self.alloc_table(level).0.invariants(),
    {
        let (s2, table) = self.alloc_table(level);
        self.alloc_table_facts(level);
        assert forall|table2: Table| #[trigger] s2.tables.contains(table2) implies table2.level
            < s2.arch.level_count() by {
            if table2 != table {
                assert(self.tables.contains(table2));
            }
        }
    }

    /// Lemma. `alloc_table` preserves accessibility.
    pub broadcast proof fn lemma_alloc_table_preserves_accessibility(
        self,
        level: nat,
        base: PAddr,
        index: nat,
    )
        requires
            self.invariants(),
            level < self.arch.level_count(),
            self.accessible(base, index),
        ensures
            #[trigger] self.alloc_table(level).0.accessible(base, index),
    {
        let (s2, new_table) = self.alloc_table(level);
        self.alloc_table_facts(level);
        // s2 contains table with base address `base`
        assert(self.contains_table(base));
        assert forall|table: Table| self.tables.contains(table) implies s2.tables.contains(
            table,
        ) by {
            let idx = choose|i| 0 <= i < self.tables.len() && self.tables[i] == table;
            assert(s2.tables[idx] == table);
        }
        assert(s2.contains_table(base));

        // The table with base address `base` is the same as the table in `s1`
        self.lemma_alloc_table_preserves_invariants(level);
        s2.lemma_table_base_unique();
        assert(self.table(base) == s2.table(base));
    }

    /// Lemma. pt_mem after `alloc_table` contains the new table.
    pub broadcast proof fn lemma_allocated_contains_new_table(self, level: nat)
        requires
            self.invariants(),
            level < self.arch.level_count(),
        ensures
            ({
                let (s2, table) = #[trigger] self.alloc_table(level);
                s2.contains_table(table.base)
            }),
    {
        let (s2, table) = self.alloc_table(level);
        self.alloc_table_facts(level);
        assert(s2.tables == self.tables.push(table));
        assert(s2.tables.last() == table);
        assert(s2.tables.contains(table));
    }

    /// Lemma. pt_mem after `alloc_table` contains all pre-existing tables.
    pub broadcast proof fn lemma_allocated_contains_old_tables(self, level: nat)
        requires
            self.invariants(),
            level < self.arch.level_count(),
        ensures
            ({
                let (s2, table) = #[trigger] self.alloc_table(level);
                forall|base: PAddr|
                    s2.contains_table(base) && base != table.base ==> self.contains_table(base)
            }),
    {
        let (s2, table) = self.alloc_table(level);
        self.alloc_table_facts(level);
        assert forall|base: PAddr|
            s2.contains_table(base) && base != table.base implies self.contains_table(base) by {
            let table = choose|table: Table| #[trigger]
                s2.tables.contains(table) && table.base == base;
            assert(self.tables.contains(table));
        }
    }

    /// Lemma. `self.tables` after `alloc_table` is a superset of before.
    pub broadcast proof fn lemma_allocated_is_superset(self, level: nat)
        requires
            self.invariants(),
            level < self.arch.level_count(),
        ensures
            ({
                let (s2, table) = #[trigger] self.alloc_table(level);
                forall|base: PAddr| self.contains_table(base) ==> s2.contains_table(base)
            }),
    {
        let (s2, table) = self.alloc_table(level);
        self.alloc_table_facts(level);
        assert forall|base: PAddr| self.contains_table(base) implies s2.contains_table(base) by {
            let i = choose|i| 0 <= i < self.tables.len() && #[trigger] self.tables[i].base == base;
            assert(s2.tables.contains(s2.tables[i]));
        }
    }

    /// Lemma. `dealloc_table` preserves invariants.
    pub broadcast proof fn lemma_dealloc_table_preserves_invariants(self, base: PAddr)
        requires
            self.invariants(),
            self.contains_table(base),
            base != self.root(),
        ensures
            #[trigger] self.dealloc_table(base).invariants(),
    {
    }

    /// Lemma. `dealloc_table` does not affect tables with different base addresses.
    pub broadcast proof fn lemma_dealloc_table_not_affect_other_tables(
        self,
        base: PAddr,
        base2: PAddr,
    )
        requires
            self.invariants(),
            self.contains_table(base),
            base != self.root(),
            self.contains_table(base2),
            base != base2,
        ensures
            #[trigger] self.dealloc_table(base).contains_table(base2),
            #[trigger] self.dealloc_table(base).table(base2) == self.table(base2),
    {
        let s2 = self.dealloc_table(base);
        let i = choose|i| 0 <= i < self.tables.len() && #[trigger] self.tables[i].base == base;
        let j = choose|j| 0 <= j < self.tables.len() && #[trigger] self.tables[j].base == base2;
        self.lemma_table_base_unique();
        assert(i != j);
        assert(s2.tables.len() == self.tables.len() - 1);
        if j < i {
            assert(s2.tables[j] == self.tables[j]);
            assert(s2.tables.contains(s2.tables[j]));
        } else {
            assert(s2.tables[j - 1] == self.tables[j]);
            assert(s2.tables.contains(s2.tables[j - 1]));
        }
    }

    /// Lemma. `write` preserves invariants.
    pub broadcast proof fn lemma_write_preserves_invariants(
        self,
        base: PAddr,
        index: nat,
        entry: u64,
    )
        requires
            self.invariants(),
            self.accessible(base, index),
        ensures
            #[trigger] self.write(base, index, entry).invariants(),
    {
        self.write_facts(base, index, entry);
    }
}

/// Broadcast page table memory related lemmas.
pub broadcast group group_pt_mem_lemmas {
    PageTableMem::table_view_facts,
    PageTableMem::alloc_table_facts,
    PageTableMem::write_facts,
    PageTableMem::lemma_table_base_unique,
    PageTableMem::lemma_contains_root,
    PageTableMem::lemma_init_implies_invariants,
    PageTableMem::lemma_alloc_table_preserves_invariants,
    PageTableMem::lemma_allocated_contains_new_table,
    PageTableMem::lemma_allocated_contains_old_tables,
    PageTableMem::lemma_allocated_is_superset,
    PageTableMem::lemma_alloc_table_preserves_accessibility,
    PageTableMem::lemma_dealloc_table_preserves_invariants,
    PageTableMem::lemma_dealloc_table_not_affect_other_tables,
    PageTableMem::lemma_write_preserves_invariants,
}

/// **EXEC-MODE** Describe a page table stored in physical memory.
pub struct TableExec {
    /// Base address of the table.
    pub base: PAddrExec,
    /// Size of the table.
    pub size: FrameSize,
    /// Level of the table.
    pub level: Ghost<nat>,
}

impl TableExec {
    /// View the concrete table as an abstract table.
    pub open spec fn view(self) -> Table {
        Table { base: self.base@, size: self.size, level: self.level@ }
    }
}

/// **EXEC-MODE** Concrete implementation of page table memory.
///
/// Page table memory manages all frames allocated for the hierarchical page tables, and
/// provides read/write, alloc/dealloc functionality.
pub struct PageTableMemExec {
    /// All tables in the hierarchical page table, the first table is the root.
    pub tables: Vec<TableExec>,
    /// Page table architecture.
    pub arch: PTArchExec,
}

impl PageTableMemExec {
    /// View the concrete page table memory as an abstract page table memory.
    pub open spec fn view(self) -> PageTableMem {
        PageTableMem {
            tables: Seq::new(self.tables.len() as nat, |i| self.tables[i]@),
            arch: self.arch@,
        }
    }

    /// Physical address of the root page table.
    pub fn root(&self) -> (res: PAddrExec)
        requires
            self.tables.len() > 0,
        ensures
            res@ == self@.root(),
    {
        self.tables[0].base
    }

    /// If a table is empty.
    #[verifier::external_body]
    pub fn is_table_empty(&self, base: PAddrExec) -> (res: bool)
        requires
            self@.contains_table(base@),
        ensures
            res == self@.is_table_empty(base@),
    {
        let table = self.tables.iter().find(|t| t.base == base).unwrap();
        let contents = unsafe {
            core::slice::from_raw_parts(base.0 as *const u8, table.size.as_usize())
        };
        // Note: verumfmt cannot parse closure in `iter().all()`
        for &byte in contents {
            if byte != 0 {
                return false;
            }
        }
        true
    }

    /// Allocate a new table and returns the table descriptor.
    ///
    /// Assumption: To satisfy the post-condition we need to assume the correctness of
    /// the memory allocator, which may be verified in the future work.
    #[verifier::external_body]
    pub fn alloc_table(&mut self, level: usize) -> (res: TableExec)
        requires
            old(self)@.invariants(),
            level < old(self)@.arch.level_count(),
        ensures
            (self@, res@) == old(self)@.alloc_table(level as nat),
    {
        unreached()
    }

    /// Deallocate a table.
    ///
    /// Assumption: To satisfy the post-condition we need to assume the correctness of
    /// the memory allocator, which may be verified in the future work.
    #[verifier::external_body]
    pub fn dealloc_table(&mut self, base: PAddrExec)
        requires
            old(self)@.invariants(),
            old(self)@.contains_table(base@),
            base@ != old(self)@.root(),
        ensures
            self@ == old(self)@.dealloc_table(base@),
    {
        unreached()
    }

    /// Get the value at the given index in the given table.
    ///
    /// Assumption: Raw memory access is assumed to be correct.
    #[verifier::external_body]
    pub fn read(&self, base: PAddrExec, index: usize) -> (res: u64)
        requires
            self@.invariants(),
            self@.accessible(base@, index as nat),
        ensures
            self@.read(base@, index as nat) == res,
    {
        unsafe { (base.0 as *const u64).offset(index as isize).read_volatile() }
    }

    /// Write the value to the given index in the given table.
    ///
    /// Assumption: Raw memory access is assumed to be correct.
    #[verifier::external_body]
    pub fn write(&mut self, base: PAddrExec, index: usize, value: u64)
        requires
            old(self)@.invariants(),
            old(self)@.accessible(base@, index as nat),
        ensures
            self@ == old(self)@.write(base@, index as nat, value),
    {
        unsafe { (base.0 as *mut u64).offset(index as isize).write_volatile(value) }
    }  // /
    // Lemma.
    // pub broadcast proof fn lemma_exec_equal_implies_spec_equal(self, base: PAddrExec)

}

} // verus!
