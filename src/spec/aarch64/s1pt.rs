//! Abstract specification of VMSAv8-64 stage 1 hardware behavior.
//!
//! - Page & Block descriptor atttributes.
//! - Page table hierarchy.
//! - Hardware behavior of page table walk.

use vstd::prelude::*;

use super::mem::PageTableMem;

verus! {

/// Abstract stage 1 VMSAv8-64 Table descriptor.
pub ghost struct GhostTableDescriptor {
    pub addr: usize,
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
    pub addr: usize,
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
    pub value: u64
}

impl PTEntry {
    /// Map the page table entry to a ghost page table entry.
    pub open spec fn view(self) -> GhostPTEntry {
        let value = self.value;

        // Check if the entry is valid (bit 0 is set)
        if value & 0x1 == 0 {
            GhostPTEntry::Empty
        } else {
            // Determine if it's a table descriptor or a page/block descriptor
            if value & 0x2 != 0 {
                // Table descriptor
                let addr = (value & 0x0000_FFFF_FFFF_F000) as usize; // Extract address bits [47:12]
                let accessed = (value & (1u64 << 10)) != 0; // AF bit
                let ns = (value & (1u64 << 5)) != 0; // NS bit
                let ap_user = (value & (1u64 << 6)) != 0; // APTable[0] bit
                let pxn = (value & (1u64 << 59)) != 0; // PXN bit
                let uxn = (value & (1u64 << 60)) != 0; // UXN bit

                GhostPTEntry::Table(GhostTableDescriptor {
                    addr,
                    accessed,
                    ns,
                    ap_user,
                    pxn,
                    uxn,
                })
            } else {
                // Page or block descriptor
                let addr = (value & 0x0000_FFFF_FFFF_F000) as usize; // Extract address bits [47:12]
                let non_block = (value & (1u64 << 1)) != 0; // Block/Page flag (bit 1)
                let accessed = (value & (1u64 << 10)) != 0; // AF bit
                let dirty = (value & (1u64 << 55)) != 0; // DBM bit
                let ap_rw = (value & (1u64 << 7)) != 0; // AP[2] bit
                let ap_user = (value & (1u64 << 6)) != 0; // AP[1] bit
                let attr_indx = ((value >> 2) & 0x7) as u8; // AttrIndx bits [4:2]
                let shareability_val = (value >> 8) & 0x3;
                let shareability = if shareability_val == 0b00 {
                    Shareability::NonShareable
                } else if shareability_val == 0b01 {
                    Shareability::OuterShareable
                } else if shareability_val == 0b10 {
                    Shareability::InnerShareable
                } else {
                    Shareability::NonShareable
                }; // Shareability bits [11:10]
                let xn = (value & (1u64 << 54)) != 0; // XN bit
                let contiguous = (value & (1u64 << 52)) != 0; // Contiguous bit
                let ns = (value & (1u64 << 5)) != 0; // NS bit

                GhostPTEntry::Page(GhostPageDescriptor {
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
                })
            }
        }
    }
}

/// Read a page table entry from the page table memory
pub open spec fn read_pt_entry(mem: PageTableMem, addr: nat) -> GhostPTEntry {
    PTEntry {
        value: mem.read(addr),
    }@
}

pub struct Frame {
    pub base: nat,
    pub size: nat
}

pub struct Flags {
    // TODO: add more fields
}

/// A mapped page or block
pub struct PageMapping {
    pub frame: Frame,
    pub flags: Flags,
}

/// Hardware behavior of valid page table walk.
/// 
/// Given a `PageTableMem` `mem`, the predicate is true for those `addr` and `page` where the
/// MMU's page table walk arrives at an entry mapping the frame `page.frame`, and the `pte.flags`
/// must reflect the properties along the translation path.
/// 
/// Only support 4-level page table walk yet.
pub open spec fn page_table_walk(mem: PageTableMem, addr: nat, page: PageMapping) -> bool {
    // TODO: suppose `mem.root` is the root addr of page table
}

} // verus!
