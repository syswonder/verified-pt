use vstd::prelude::*;

use super::mem::PageTableMem;

verus! {

/// Abstract stage 1 VMSAv8-64 Table descriptor.
pub ghost struct GhostTableDescriptor {
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
pub ghost struct GhostPageDescriptor {
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
    /// Shareability domain
    pub shareability: Shareability,
    /// Execute Never (XN)
    pub xn: bool,
    /// Contiguous bit hint
    pub contiguous: bool,
    /// Non-secure bit
    pub ns: bool,
}

/// Shareability domain specification
#[derive(PartialEq, Eq)]
pub ghost enum Shareability {
    NonShareable,
    OuterShareable,
    InnerShareable,
}

/// Abstract definition of page table entry.
pub ghost enum GhostPTEntry {
    /// Points to next level page table
    Table(GhostTableDescriptor),
    /// Maps physical page/block with attributes
    Page(GhostPageDescriptor),
    /// Invalid/empty entry
    Empty,
}

/// Concrete page table entry
pub struct PTEntry {
    pub value: u64,
}

impl PTEntry {
    /// Maps the concrete page table entry to its abstract representation.
    ///
    /// # Returns
    /// - `GhostPTEntry::Table` if the entry is a valid table descriptor.
    /// - `GhostPTEntry::Page` if the entry is a valid page/block descriptor.
    /// - `GhostPTEntry::Empty` if the entry is invalid or empty.
    pub open spec fn view(self) -> GhostPTEntry {
        let value = self.value;
        if value & 0x1 == 0 {
            GhostPTEntry::Empty
        } else {
            if value & 0x2 != 0 {
                let addr = (value & 0x0000_FFFF_FFFF_F000) >> 12;
                let accessed = (value & (1u64 << 10)) != 0;
                let ns = (value & (1u64 << 5)) != 0;
                let ap_user = (value & (1u64 << 6)) != 0;
                let pxn = (value & (1u64 << 59)) != 0;
                let uxn = (value & (1u64 << 60)) != 0;
                GhostPTEntry::Table(GhostTableDescriptor { addr, accessed, ns, ap_user, pxn, uxn })
            } else {
                let addr = (value & 0x0000_FFFF_FFFF_F000) >> 12;
                let non_block = (value & (1u64 << 1)) != 0;
                let accessed = (value & (1u64 << 10)) != 0;
                let dirty = (value & (1u64 << 55)) != 0;
                let ap_rw = (value & (1u64 << 7)) != 0;
                let ap_user = (value & (1u64 << 6)) != 0;
                let attr_indx = ((value >> 2) & 0x7) as u8;
                let shareability_val = (value >> 8) & 0x3;
                let shareability = if shareability_val == 1 {
                    Shareability::OuterShareable
                } else if shareability_val == 2 {
                    Shareability::InnerShareable
                } else {
                    Shareability::NonShareable
                };
                let xn = (value & (1u64 << 54)) != 0;
                let contiguous = (value & (1u64 << 52)) != 0;
                let ns = (value & (1u64 << 5)) != 0;
                GhostPTEntry::Page(
                    GhostPageDescriptor {
                        addr,
                        non_block,
                        accessed,
                        dirty,
                        ap_rw,
                        ap_user,
                        attr_indx,
                        shareability,
                        xn,
                        contiguous,
                        ns,
                    },
                )
            }
        }
    }
}

/// Reads a page table entry from the page table memory.
///
/// # Parameters
/// - `mem`: The page table memory to read from.
/// - `addr`: The address of the page table entry to read.
///
/// # Returns
/// - The abstract representation of the page table entry (`GhostPTEntry`).
pub open spec fn read_pt_entry(mem: PageTableMem, addr: u64) -> GhostPTEntry {
    PTEntry { value: mem.read(addr) }@
}

/// Represents a physical memory frame.
pub struct Frame {
    /// The base address of the frame.
    pub base: nat,
    /// The size of the frame in bytes.
    pub size: nat,
}

/// Represents memory access and attribute flags.
#[derive(PartialEq, Eq)]
pub struct Flags {
    /// Whether the memory is readable.
    pub readable: bool,
    /// Whether the memory is writable.
    pub writable: bool,
    /// Whether the memory is executable in user mode.
    pub executable_user: bool,
    /// Whether the memory is executable in kernel mode.
    pub executable_kernel: bool,
    /// Whether the memory is accessible in user mode.
    pub user_accessible: bool,
    /// Memory attribute index (AttrIndx).
    pub attr_indx: u8,
    /// Shareability domain of the memory.
    pub shareability: Shareability,
    /// Non-secure bit (NS).
    pub ns: bool,
    /// Contiguous bit hint.
    pub contiguous: bool,
    /// Dirty bit (DBM).
    pub dirty: bool,
    /// Accessed bit (AF).
    pub accessed: bool,
}

/// Represents a mapping between a virtual address and a physical frame.
pub struct PageMapping {
    /// The physical frame being mapped.
    pub frame: Frame,
    /// The flags associated with the mapping.
    pub flags: Flags,
}

/// Extract index bits from virtual address for given level (0-3)
spec fn get_index(addr: u64, level: nat) -> u64 {
    let level_shift = 39 - level * 9;
    (addr >> level_shift) & 0x1FF
}

/// Compute physical address and flags for page table walk
spec fn compute_mapping(
    entry: GhostPageDescriptor,
    level: nat,
    addr: u64,
    user_ok: bool,
    uxn_accum: bool,
    pxn_accum: bool,
) -> (Frame, Flags) {
    let page_size = (1 << (12 + 9 * (3 - level as u64))) as u64;
    let offset_mask: u64 = (page_size - 1) as u64;
    let base = (entry.addr << 12) | (addr & offset_mask);
    let flags = Flags {
        readable: true,
        writable: entry.ap_rw,
        executable_user: !(uxn_accum || entry.xn),
        executable_kernel: !pxn_accum,
        user_accessible: user_ok && entry.ap_user,
        attr_indx: entry.attr_indx,
        shareability: entry.shareability,
        ns: entry.ns,
        contiguous: entry.contiguous,
        dirty: entry.dirty,
        accessed: entry.accessed,
    };
    (Frame { base: base as nat, size: page_size as nat }, flags)
}

/// Recursive helper for page table walk
pub closed spec fn walk_level(
    mem: PageTableMem,
    addr: u64,
    level: nat,
    table_addr: u64,
    user_ok: bool,
    uxn_accum: bool,
    pxn_accum: bool,
) -> Option<PageMapping>
    decreases level,
{
    if level == 0 {
        None
    } else {
        let index = get_index(addr, level);
        let pte_addr = (table_addr + index * 8) as u64;
        let pte = read_pt_entry(mem, pte_addr);

        match pte {
            GhostPTEntry::Table(desc) => {
                let new_user_ok = user_ok && desc.ap_user;
                let new_uxn = uxn_accum || desc.uxn;
                let new_pxn = pxn_accum || desc.pxn;
                let next_table = desc.addr << 12;
                walk_level(mem, addr, (level - 1) as nat, next_table, new_user_ok, new_uxn, new_pxn)
            },
            GhostPTEntry::Page(page_desc) => {
                if level > 3 && page_desc.non_block {
                    None  // Block must be at level 1-3, page only at level 1

                } else {
                    let (frame, flags) = compute_mapping(
                        page_desc,
                        level,
                        addr,
                        user_ok,
                        uxn_accum,
                        pxn_accum,
                    );
                    Some(PageMapping { frame, flags })
                }
            },
            GhostPTEntry::Empty => None,
        }
    }
}

/// Hardware behavior of a valid page table walk.
///
/// This function simulates the MMU's page table walk process and checks if the given
/// virtual address `addr` maps to the specified `page` with the correct flags.
///
/// Given a `PageTableMem` `mem`, the predicate is true for those `addr` and `page` where the
/// MMU's page table walk arrives at an entry mapping the frame `page.frame`, and the `pte.flags`
/// must reflect the properties along the translation path.
///
/// Support 4-level page tables yet.
///
/// # Parameters
/// - `mem`: The page table memory to walk.
/// - `addr`: The virtual address to translate.
/// - `page`: The expected page mapping to validate against.
///
/// # Returns
/// - `true` if the page table walk results in a valid mapping that matches `page`.
/// - `false` otherwise.
pub open spec fn page_table_walk(mem: PageTableMem, addr: u64, page: PageMapping) -> bool {
    let root_addr = mem.root();
    match walk_level(mem, addr, 4, root_addr, true, false, false) {
        Some(mapping) => {
            &&& mapping.frame.base == page.frame.base
            &&& mapping.frame.size == page.frame.size
            &&& mapping.flags == page.flags
        },
        None => false,
    }
}

} // verus!
