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
    arch::PTArch,
    frame::{Frame, FrameAttr, FrameSize},
    nat_to_u64,
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
    /// Root page table.
    pub open spec fn root(self) -> Table {
        self.tables[0]
    }

    /// Get the table with the given base address.
    pub open spec fn table(self, base: PAddr) -> Table
        recommends
            exists|table| #[trigger] self.tables.contains(table) && table.base == base,
    {
        choose|table: Table| #[trigger] self.tables.contains(table) && table.base == base
    }

    /// View a table as a sequence of entries.
    pub open spec fn table_view(self, table: Table) -> Seq<u64>
        recommends
            self.tables.contains(table),
    ;

    /// Read the entry at the given index in the given table.
    pub open spec fn read(self, table: Table, index: nat) -> u64
        recommends
            self.tables.contains(table),
            index < self.arch.entry_count(table.level),
    {
        self.table_view(table)[index as int]
    }

    /// Interpret as `(vbase, frame)` mappings.
    ///
    /// This function extracts all mappings that valid hardware page table walks can reach.
    /// Hardware behavior is specified by the `walk` function.
    pub open spec fn interpret(self) -> Map<VAddr, Frame> {
        let max_vaddr: nat = 0x8000_0000;
        Map::new(
            |addr: VAddr|
                addr.0 < max_vaddr && exists|frame: Frame| #[trigger]
                    self.walk(nat_to_u64(addr.0), frame),
            |addr: VAddr| choose|frame: Frame| #[trigger] self.walk(nat_to_u64(addr.0), frame),
        )
    }

    /// Hardware behavior of a 4-level page table walk process.
    ///
    /// This function simulates the MMU's page table walk process and checks if the given
    /// virtual address `addr` maps to the specified `frame` with the correct flags.
    ///
    /// Given a `PageTableMem` `pt_mem`, the predicate is true for those `addr` and `frame` where the
    /// MMU's page table walk arrives at an entry mapping the frame `frame`, and the `pte.flags`
    /// must reflect the properties along the translation path.
    pub open spec fn walk(self, addr: u64, frame: Frame) -> bool {
        match self.walk_level(addr, self.arch.level_count(), self.root(), true, false, false) {
            Some(reached) => {
                &&& reached.base == frame.base
                &&& reached.size == frame.size
                &&& reached.attr == frame.attr
            },
            None => false,
        }
    }

    /// Recursive helper for page table walk.
    ///
    /// TODO: this function yet only supports 48-bit VA and 4-level page tables.
    /// The implementation should correspond to the `arch` field.
    pub closed spec fn walk_level(
        self,
        addr: u64,
        level: nat,
        table: Table,
        user_ok: bool,
        uxn_accum: bool,
        pxn_accum: bool,
    ) -> Option<Frame>
        decreases level,
    {
        if level == 0 {
            None
        } else {
            let level_shift = 3 + level * 9;
            let index = (addr >> level_shift) & 0x1FF;
            let pte = S1PTEntry(self.read(table, index as nat))@;
            match pte {
                GhostS1PTEntry::Table(desc) => {
                    let new_user_ok = user_ok && desc.ap_user;
                    let new_uxn = uxn_accum || desc.uxn;
                    let new_pxn = pxn_accum || desc.pxn;
                    let next_table = self.table(PAddr((desc.addr << 12) as nat));
                    self.walk_level(
                        addr,
                        (level - 1) as nat,
                        next_table,
                        new_user_ok,
                        new_uxn,
                        new_pxn,
                    )
                },
                GhostS1PTEntry::Page(page_desc) => {
                    if level > 3 && page_desc.non_block {
                        // Block must be at level 1-3, page only at level 1
                        None
                    } else {
                        Some(
                            Self::compute_frame(
                                page_desc,
                                level,
                                addr,
                                user_ok,
                                uxn_accum,
                                pxn_accum,
                            ),
                        )
                    }
                },
                GhostS1PTEntry::Empty => None,
            }
        }
    }

    /// Compute physical address and flags for the reached frame.
    spec fn compute_frame(
        entry: GhostS1PageDescriptor,
        level: nat,
        addr: u64,
        user_ok: bool,
        uxn_accum: bool,
        pxn_accum: bool,
    ) -> Frame {
        let size = if level == 3 {
            FrameSize::Size1G
        } else if level == 2 {
            FrameSize::Size2M
        } else {
            FrameSize::Size4K
        };
        let offset_mask = (size.as_u64() - 1) as u64;
        let base = PAddr(((entry.addr << 12) | (addr & offset_mask)) as nat);
        let attr = FrameAttr {
            readable: true,
            writable: entry.ap_rw,
            // NOTE: VMSA-v8 differentiates between user-executable and kernel-executable
            // We don't have this distinction yet, so we just use the user-executable bit
            executable: !(uxn_accum || entry.xn),
            user_accessible: user_ok && entry.ap_user,
        };
        Frame { base, size, attr }
    }

    /// Invariants.
    pub open spec fn invariants(self) -> bool {
        &&& self.arch.invariants()
        // Root table is always present.
        &&& self.tables.len() > 0
        // Table size is valid.
        &&& forall|table: Table| #[trigger]
            self.tables.contains(table) ==> table.size.as_nat() == self.arch.table_size(
                table.level,
            )
        // All tables should not overlap.
        &&& forall|table1: Table, table2: Table| #[trigger]
            self.tables.contains(table1) && #[trigger] self.tables.contains(table2)
                ==> !PAddr::overlap(
                table1.base,
                table1.size.as_nat(),
                table2.base,
                table2.size.as_nat(),
            )
    }

    /// Init State.
    pub open spec fn init(self) -> bool {
        &&& self.arch.invariants()
        &&& self.tables.len() == 1
        &&& self.root().size.as_nat() == self.arch.table_size(0)
    }

    /// Alloc a new table.
    pub open spec fn alloc_table(s1: Self, s2: Self, level: nat, res: Table) -> bool {
        &&& s2.arch == s1.arch
        // `s1` doesn't have the table
        &&& !s1.tables.contains(res)
        // update `tables`
        &&& s2.tables == s1.tables.push(res)
        // check size
        &&& res.size.as_nat() == s1.arch.table_size(
            level,
        )
        // new table is aligned
        &&& res.base.aligned(res.size.as_nat())
        // new table is empty
        &&& s2.table_view(res) == Seq::<u64>::empty()
    }

    /// Dealloc a table.
    pub open spec fn dealloc_table(s1: Self, s2: Self, table: Table) -> bool {
        &&& s2.arch == s1.arch
        // `s1` has the table
        &&& s1.tables.contains(table)
        // update `tables`
        &&& s2.tables == s1.tables.remove_value(table)
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

    /// Dealloc a table.
    ///
    /// Assumption: To satisfy the post-condition we need to assume the correctness of
    /// the memory allocator, which may be verified in the future work.
    #[verifier::external_body]
    pub fn dealloc_table(&mut self, table: TableExec)
        requires
            old(self)@.invariants(),
        ensures
            self@.invariants(),
            PageTableMem::dealloc_table(old(self)@, self@, table@),
    {
        unreached()
    }

    /// Get the value at the given index in the given table.
    ///
    /// Assumption: Raw memory access is assumed to be valid.
    #[verifier::external_body]
    pub fn read(&self, base: PAddrExec, index: usize) -> (res: u64)
        requires
            exists|table: Table| #[trigger] self@.tables.contains(table) && table.base == base@,
            ({
                let table = choose|table: Table| #[trigger]
                    self@.tables.contains(table) && table.base == base@;
                index < self@.table_view(table).len()
            }),
        ensures
            ({
                let table = choose|table: Table| #[trigger]
                    self@.tables.contains(table) && table.base == base@;
                self@.table_view(table)[index as int] == res
            }),
    {
        unsafe { (base.0 as *const u64).offset(index as isize).read_volatile() }
    }

    /// Write the value to the given index in the given table.
    ///
    /// Assumption: Raw memory access is assumed to be valid.
    #[verifier::external_body]
    pub fn write(&self, base: PAddrExec, index: usize, value: u64)
        requires
            exists|table: Table| #[trigger] self@.tables.contains(table) && table.base == base@,
            ({
                let table = choose|table: Table| #[trigger]
                    self@.tables.contains(table) && table.base == base@;
                index < self@.table_view(table).len()
            }),
        ensures
            ({
                let table = choose|table: Table| #[trigger]
                    self@.tables.contains(table) && table.base == base@;
                self@.table_view(table)[index as int] == value
            }),
    {
        unsafe { (base.0 as *mut u64).offset(index as isize).write_volatile(value) }
    }
}

/// Abstract stage 1 VMSAv8-64 Table descriptor.
pub ghost struct GhostS1TableDescriptor {
    /// Physical address of the table
    pub addr: u64,
    /// Accessed flag (AF) - indicates if table has been accessed
    pub accessed: bool,
    /// Non-secure bit - security state attribution
    pub ns: bool,
    /// Access permissions for next level (APTable):
    /// false = Privileged access only, true = User accessible
    pub ap_user: bool,
    /// Execute permission for next level:
    /// Privileged Execute Never (PXN)
    pub pxn: bool,
    /// Execute permission for next level:
    /// User Execute Never (UXN)
    pub uxn: bool,
}

/// Abstract stage 1 VMSAv8-64 Page & Block descriptor.
pub ghost struct GhostS1PageDescriptor {
    /// Physical address of the page or block
    pub addr: u64,
    /// Block or page flag (true = Page, false = Block)
    pub non_block: bool,
    /// Accessed flag (AF)
    pub accessed: bool,
    /// Hardware managed dirty flag (DBM)
    pub dirty: bool,
    /// Access permissions:
    /// AP[2:1] encoded (false = ReadOnly, true = ReadWrite)
    pub ap_rw: bool,
    /// Access permissions:
    /// AP[0] encoded (false = Kernel only, true = User accessible)
    pub ap_user: bool,
    /// Memory attributes index (AttrIndx)
    pub attr_indx: u8,
    /// Execute Never (XN)
    pub xn: bool,
    /// Contiguous bit hint
    pub contiguous: bool,
    /// Non-secure bit
    pub ns: bool,
}

/// Abstract page table entry.
pub ghost enum GhostS1PTEntry {
    /// Points to next level page table
    Table(GhostS1TableDescriptor),
    /// Maps physical page/block with attributes
    Page(GhostS1PageDescriptor),
    /// Invalid/empty entry
    Empty,
}

/// Concrete stage-1 page table entry, wrapping a 64-bit value.
pub struct S1PTEntry(pub u64);

impl S1PTEntry {
    /// Maps the concrete page table entry to its abstract representation.
    ///
    /// # Returns
    /// - `GhostPTEntry::Table` if the entry is a valid table descriptor.
    /// - `GhostPTEntry::Page` if the entry is a valid page/block descriptor.
    /// - `GhostPTEntry::Empty` if the entry is invalid or empty.
    pub open spec fn view(self) -> GhostS1PTEntry {
        let value = self.0;
        if value & 0x1 == 0 {
            GhostS1PTEntry::Empty
        } else {
            if value & 0x2 != 0 {
                let addr = (value & 0x0000_FFFF_FFFF_F000) >> 12;
                let accessed = (value & (1u64 << 10)) != 0;
                let ns = (value & (1u64 << 5)) != 0;
                let ap_user = (value & (1u64 << 6)) != 0;
                let pxn = (value & (1u64 << 59)) != 0;
                let uxn = (value & (1u64 << 60)) != 0;
                GhostS1PTEntry::Table(
                    GhostS1TableDescriptor { addr, accessed, ns, ap_user, pxn, uxn },
                )
            } else {
                let addr = (value & 0x0000_FFFF_FFFF_F000) >> 12;
                let non_block = (value & (1u64 << 1)) != 0;
                let accessed = (value & (1u64 << 10)) != 0;
                let dirty = (value & (1u64 << 55)) != 0;
                let ap_rw = (value & (1u64 << 7)) != 0;
                let ap_user = (value & (1u64 << 6)) != 0;
                let attr_indx = ((value >> 2) & 0x7) as u8;
                let xn = (value & (1u64 << 54)) != 0;
                let contiguous = (value & (1u64 << 52)) != 0;
                let ns = (value & (1u64 << 5)) != 0;
                GhostS1PTEntry::Page(
                    GhostS1PageDescriptor {
                        addr,
                        non_block,
                        accessed,
                        dirty,
                        ap_rw,
                        ap_user,
                        attr_indx,
                        xn,
                        contiguous,
                        ns,
                    },
                )
            }
        }
    }
}

/// Abstract stage 2 VMSAv8-64 Table descriptor.
pub ghost struct GhostS2TableDescriptor {
    /// Next-level table address
    pub addr: u64,
    /// Stage 2 Access Permissions (S2AP) for next level: 2 bits
    pub s2ap: u8,
    /// Shareability (SH) attributes: 2 bits
    pub sh: u8,
    /// Accessed flag (AF)
    pub af: bool,
    /// Non-secure bit
    pub ns: bool,
}

/// Abstract stage 2 VMSAv8-64 Page & Block descriptor.
pub ghost struct GhostS2PageDescriptor {
    /// Physical address of the page or block
    pub addr: u64,
    /// Page/Block type (true = Page, false = Block)
    pub is_page: bool,
    /// Stage 2 Access Permissions (S2AP): 2 bits
    pub s2ap: u8,
    /// Shareability (SH) attributes: 2 bits
    pub sh: u8,
    /// Accessed flag (AF)
    pub af: bool,
    /// Memory attributes index (AttrIndx)
    pub attr_indx: u8,
    /// Non-secure bit
    pub ns: bool,
}

/// Abstract stage 2 page table entry.
pub ghost enum GhostS2PTEntry {
    /// Points to next level page table
    Table(GhostS2TableDescriptor),
    /// Maps physical page/block with attributes
    Page(GhostS2PageDescriptor),
    /// Invalid/empty entry
    Empty,
}

/// Concrete page table entry.
pub struct S2PTEntry(pub u64);

impl S2PTEntry {
    /// Maps the concrete page table entry to its abstract representation.
    pub open spec fn view(self) -> GhostS2PTEntry {
        let value = self.0;
        if value & 0x1 == 0 {
            GhostS2PTEntry::Empty
        } else if (value & 0x3) == 0x3 {
            // Table descriptor (S2AP[1:0], SH[1:0], AF, NS)
            let addr = (value & 0x0000_FFFF_FFFF_F000) >> 12;
            let s2ap = ((value >> 6) & 0x3) as u8;
            let sh = ((value >> 8) & 0x3) as u8;
            let af = (value & (1 << 10) as u64) != 0;
            let ns = (value & (1 << 5) as u64) != 0;
            GhostS2PTEntry::Table(GhostS2TableDescriptor { addr, s2ap, sh, af, ns })
        } else if (value & 0x3) == 0x1 {
            // Block/Page descriptor (S2AP[1:0], SH[1:0], AF, AttrIndx, NS)
            let addr = (value & 0x0000_FFFF_FFFF_F000) >> 12;
            let s2ap = ((value >> 6) & 0x3) as u8;
            let sh = ((value >> 8) & 0x3) as u8;
            let af = (value & (1 << 10) as u64) != 0;
            let attr_indx = ((value >> 2) & 0x7) as u8;
            let ns = (value & (1 << 5) as u64) != 0;
            GhostS2PTEntry::Page(
                GhostS2PageDescriptor {
                    addr,
                    is_page: false,  // 0x1 indicates Block
                    s2ap,
                    sh,
                    af,
                    attr_indx,
                    ns,
                },
            )
        } else {
            GhostS2PTEntry::Empty
        }
    }
}

} // verus!
