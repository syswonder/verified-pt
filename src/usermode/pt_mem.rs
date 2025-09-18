//! An easy executable page table memory implementation.
//!
//! Page Table Memory is a collection of page tables, and provides read/write, alloc/dealloc functionality.
//! The implementation should refine the specification defined in `spec::memory::PageTableMem`.
use vstd::prelude::*;

extern crate alloc;

use super::pool::FramePool;
use crate::common::{addr::PAddrExec, arch::PTArchExec, frame::FrameSize};
use crate::spec::memory::{PageTableMem, PageTableMemExec, Table};
use alloc::{boxed::Box, vec::Vec};

verus! {

/// Describe a page table stored in physical memory.
#[derive(Clone, Copy)]
pub struct TableExec {
    /// Base address of the table.
    pub base: PAddrExec,
    /// Size of the table.
    pub size: FrameSize,
    /// Level of the table.
    pub level: usize,
}

impl TableExec {
    /// View the concrete table as an abstract table.
    pub open spec fn view(self) -> Table {
        Table { base: self.base@, size: self.size, level: self.level as nat }
    }
}

#[verifier::external_type_specification]
pub struct ExFramePool(FramePool);

/// Concrete implementation of page table memory using a easy frame pool.
pub struct PooledPageTableMem {
    /// All tables in the hierarchical page table, the first table is the root.
    pub tables: Vec<TableExec>,
    /// Page table architecture.
    pub arch: PTArchExec,
    /// Frame pool for allocating/deallocating frames.
    pub pool: Box<FramePool>,
}

impl PageTableMemExec for PooledPageTableMem {
    /// View the concrete page table memory as an abstract page table memory.
    open spec fn view(self) -> PageTableMem {
        PageTableMem {
            tables: Seq::new(self.tables.len() as nat, |i| self.tables[i]@),
            arch: self.arch@,
        }
    }

    /// Physical address of the root page table.
    fn root(&self) -> (res: PAddrExec) {
        self.tables[0].base
    }

    /// If a table is empty.
    #[verifier::external_body]
    fn is_table_empty(&self, base: PAddrExec) -> (res: bool) {
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

    /// Construct a new page table memory and initialize the root table.
    #[verifier::external_body]
    fn new_init(arch: PTArchExec) -> (res: PooledPageTableMem) {
        // TODO: only support 4k frame size for now
        let mut pool = Box::new(FramePool::new());
        let base = pool.alloc();
        let table = TableExec { base, size: FrameSize::Size4K, level: 0 };
        PooledPageTableMem { tables: vec![table], arch, pool }
    }

    /// Allocate a new table and returns the table descriptor.
    ///
    /// Assumption: To satisfy the post-condition we need to assume the correctness of
    /// the memory allocator, which may be verified in the future work.
    #[verifier::external_body]
    fn alloc_table(&mut self, level: usize) -> (res: (PAddrExec, FrameSize)) {
        let _size = self.arch.frame_size(level).as_usize();
        // TODO: only support 4k frame size for now
        let base = self.pool.alloc();
        let table = TableExec { base, size: FrameSize::Size4K, level };
        self.tables.push(table);
        println!("Allocate table at {:#x}", base.0);
        (table.base, table.size)
    }

    /// Deallocate a table.
    ///
    /// Assumption: To satisfy the post-condition we need to assume the correctness of
    /// the memory allocator, which may be verified in the future work.
    #[verifier::external_body]
    fn dealloc_table(&mut self, base: PAddrExec) {
        self.tables.retain(|t| t.base != base);
        self.pool.dealloc(base);
        println!("Deallocate table at {:#x}", base.0);
    }

    /// Get the value at the given index in the given table.
    ///
    /// Assumption: Raw memory access is assumed to be correct.
    #[verifier::external_body]
    fn read(&self, base: PAddrExec, index: usize) -> (res: u64) {
        unsafe { (base.0 as *const u64).offset(index as isize).read_volatile() }
    }

    /// Write the value to the given index in the given table.
    ///
    /// Assumption: Raw memory access is assumed to be correct.
    #[verifier::external_body]
    fn write(&mut self, base: PAddrExec, index: usize, value: u64) {
        unsafe { (base.0 as *mut u64).offset(index as isize).write_volatile(value) }
    }
}

} // verus!
