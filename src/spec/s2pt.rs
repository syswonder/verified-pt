//! Stage-2 VMSAv8-64 page table walk functions.
use vstd::prelude::*;

verus! {

/// Abstract stage 2 VMSAv8-64 Table descriptor.
pub ghost struct GhostTableDescriptor {
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
pub ghost struct GhostPageDescriptor {
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

/// Abstract page table entry.
pub ghost enum GhostPTEntry {
    /// Points to next level page table
    Table(GhostTableDescriptor),
    /// Maps physical page/block with attributes
    Page(GhostPageDescriptor),
    /// Invalid/empty entry
    Empty,
}

/// Concrete page table entry.
pub struct PTEntry {
    pub value: u64,
}

impl PTEntry {
    /// Maps the concrete page table entry to its abstract representation.
    pub open spec fn view(self) -> GhostPTEntry {
        let value = self.value;
        if value & 0x1 == 0 {
            GhostPTEntry::Empty
        } else if (value & 0x3) == 0x3 {
            // Table descriptor (S2AP[1:0], SH[1:0], AF, NS)
            let addr = (value & 0x0000_FFFF_FFFF_F000) >> 12;
            let s2ap = ((value >> 6) & 0x3) as u8;
            let sh = ((value >> 8) & 0x3) as u8;
            let af = (value & (1 << 10) as u64) != 0;
            let ns = (value & (1 << 5) as u64) != 0;
            GhostPTEntry::Table(GhostTableDescriptor { addr, s2ap, sh, af, ns })
        } else if (value & 0x3) == 0x1 {
            // Block/Page descriptor (S2AP[1:0], SH[1:0], AF, AttrIndx, NS)
            let addr = (value & 0x0000_FFFF_FFFF_F000) >> 12;
            let s2ap = ((value >> 6) & 0x3) as u8;
            let sh = ((value >> 8) & 0x3) as u8;
            let af = (value & (1 << 10) as u64) != 0;
            let attr_indx = ((value >> 2) & 0x7) as u8;
            let ns = (value & (1 << 5) as u64) != 0;
            GhostPTEntry::Page(
                GhostPageDescriptor {
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
            GhostPTEntry::Empty
        }
    }
}

} // verus!
