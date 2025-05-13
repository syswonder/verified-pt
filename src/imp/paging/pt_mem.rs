//! Page table memory implementation.
//!
//! Page table memory is a memory region that stores page tables, allocated by the memory allocator.
//! Hardware access page table memory and performs page table walks to translate VA to PA.
//! To satisfies the specification defined in `spec::hardware`, the correctness of the memory allocator
//! and raw memory access is assumed.
//!
//! Page table memory is designed to be architecture independent, but yet only supports VMSAv8-64.
use vstd::{pervasive::unreached, prelude::*};

use super::arch::{lemma_vmsav8_4k_arch_valid, VMSAV8_4K_ARCH};
use crate::{
    common::{addr::PAddrExec, arch::PTArch, frame::FrameSize},
    spec::memory::{PageTableMem, Table},
};

verus! {

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

    /// Create an empty page table memory that only contains root table.
    pub fn new_vmsav8_4k(root: PAddrExec) -> (res: Self)
        ensures
            res@.arch == VMSAV8_4K_ARCH,
            res@.init(),
    {
        let root_table = TableExec { base: root, size: FrameSize::Size4K, level: Ghost(0) };
        let res = Self { tables: vec![root_table], arch: Ghost(VMSAV8_4K_ARCH) };
        proof {
            lemma_vmsav8_4k_arch_valid();
            // Assume init value of page table memory
            assume(res@.table_view(res@.root()) == seq![0u64; res@.arch.entry_count(0)]);
        }
        res
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
