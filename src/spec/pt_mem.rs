//! Page table memory specification and implementation.
//!
//! Page table memory is a memory region that stores page tables, allocated by the memory allocator.
//! Hardware access page table memory and performs page table walks to translate VA to PA.
//! To obtain some properties of page table memory, the correctness of the moemory allocator and raw
//! memory access is assumed.
//!
//! Page table memory is designed to be architecture independent, but yet only supports VMSAv8-64.
use vstd::{pervasive::unreached, prelude::*};

use super::{
    addr::{PAddr, PAddrExec, VAddr},
    arch::{lemma_vmsav8_4k_arch_valid, PTArch, VMSAV8_4K_ARCH},
    frame::{Frame, FrameSize},
};

verus! {

/// Describe a page table stored in physical memory.
pub struct Table {
    /// Base address of the table.
    pub base: PAddr,
    /// Size of the table.
    pub size: FrameSize,
    /// Level of the table.
    pub level: nat,
}

/// Abstract model of page table memory.
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

    /// Root page table.
    pub open spec fn root_table(self) -> Table {
        self.tables[0]
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

    /// If accessing the given table at the given index is allowed.
    pub open spec fn accessible(self, base: PAddr, index: nat) -> bool {
        self.contains_table(base) && index < self.arch.entry_count(self.table(base).level)
    }

    /// If the table is a leaf table.
    pub open spec fn is_leaf(self, base: PAddr) -> bool {
        self.contains_table(base) && self.table(base).level == self.arch.level_count() - 1
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
    /// Hardware behavior is not specified yet.
    pub open spec fn interpret(self) -> Map<VAddr, Frame>;

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
    {
        assert(self.tables.contains(self.tables[0]));
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
    pub arch: Ghost<PTArch>,
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

    /// An empty page table memory that only contains root table.
    pub fn new_vmsav8_4k(root: PAddrExec) -> (res: Self)
        ensures
            res@.init(),
    {
        let root_table = TableExec { base: root, size: FrameSize::Size4K, level: Ghost(0) };
        proof {
            lemma_vmsav8_4k_arch_valid();
        }
        Self { tables: vec![root_table], arch: Ghost(VMSAV8_4K_ARCH) }
    }

    /// Alloc a new table and returns the table descriptor.
    ///
    /// Assumption: To satisfy the post-condition we need to assume the correctness of
    /// the memory allocator, which may be verified in the future work.
    #[verifier::external_body]
    pub fn alloc_table(&mut self, level: u64) -> (res: TableExec)
        requires
            old(self)@.invariants(),
        ensures
            self@.invariants(),
            PageTableMem::alloc_table(old(self)@, self@, level as nat, res@),
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
            PageTableMem::write(old(self)@, self@, base@, index as nat, value),
    {
        unsafe { (base.0 as *mut u64).offset(index as isize).write_volatile(value) }
    }
}

} // verus!
