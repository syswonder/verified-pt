//! Executable page table memory implementation.
//!
//! Page Table Memory is a collection of page tables, and provides read/write, alloc/dealloc functionality.
//! The implementation should refine the specification defined in `spec::memory::PageTableMem`.
use vstd::prelude::*;

use crate::common::{addr::PAddrExec, arch::PTArchExec, frame::FrameSize};
use crate::spec::memory::{PageTableMem, Table};

verus! {

/// Describe a page table stored in physical memory.
#[derive(Clone, Copy)]
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

#[verifier::external_type_specification]
pub struct ExFramePool(FramePool);

/// Concrete implementation of page table memory.
///
/// Page table memory manages all frames allocated for the hierarchical page tables, and
/// provides read/write, alloc/dealloc functionality.
pub struct PageTableMemExec {
    /// All tables in the hierarchical page table, the first table is the root.
    pub tables: Vec<TableExec>,
    /// Page table architecture.
    pub arch: PTArchExec,
    /// Frame pool for allocating/deallocating frames.
    pub pool: Box<FramePool>,
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

    /// Construct a new page table memory and initialize the root table.
    #[verifier::external_body]
    pub fn new_init(arch: PTArchExec) -> (res: PageTableMemExec)
        requires
            arch@.valid(),
        ensures
            res@.init(),
    {
        // TODO: only support 4k frame size for now
        let mut pool = Box::new(FramePool::new());
        let base = pool.alloc();
        let table = TableExec { base, size: FrameSize::Size4K, level: Ghost(0nat) };
        PageTableMemExec { tables: vec![table], arch, pool }
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
        let _size = self.arch.frame_size(level).as_usize();
        // TODO: only support 4k frame size for now
        let base = self.pool.alloc();
        let table = TableExec { base, size: FrameSize::Size4K, level: Ghost(level as nat) };
        self.tables.push(table);
        println!("Allocate table at {:#x}", base.0);
        table
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
        self.tables.retain(|t| t.base != base);
        self.pool.dealloc(base);
        println!("Deallocate table at {:#x}", base.0);
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
        let r = unsafe { (base.0 as *const u64).offset(index as isize).read_volatile() };
        println!("read {:#x} from {:#x}", r, base.0 + index * 8);
        r
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
        println!("write {:#x} to {:#x}", value, base.0 + index * 8);
        unsafe { (base.0 as *mut u64).offset(index as isize).write_volatile(value) }
    }
}

} // verus!

/// An easy memory pool that uses bitmap to track 4k physical frames.
pub struct FramePool {
    /// Memory region.
    #[repr(C, align(4096))]
    pub mem: [u8; 0x100000],
    /// Bitmap of the physical frames.
    pub bitmap: [bool; 0x100],
}

impl FramePool {
    /// Create a new frame pool.
    pub fn new() -> Self {
        Self {
            bitmap: [false; 0x100],
            mem: [0; 0x100000],
        }
    }

    /// Allocate a 4k physical frame.
    fn alloc(&mut self) -> PAddrExec {
        let idx = self.bitmap.iter().position(|b| !b).unwrap();
        self.bitmap[idx] = true;
        PAddrExec(self.mem.as_ptr() as usize + idx as usize * 4096)
    }

    /// Deallocate a 4k physical frame.
    fn dealloc(&mut self, addr: PAddrExec) {
        let idx = (addr.0 - self.mem.as_ptr() as usize) / 4096;
        self.bitmap[idx] = false;
    }
}