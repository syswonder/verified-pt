//! Stage-1 VMSAv8-64 page table specification.
use vstd::prelude::*;

use super::{
    addr::{PAddr, PAddrExec, VAddr},
    frame::{Frame, FrameAttr, FrameExec, FrameSize},
    nat_to_u64,
};

verus! {

/// Stage-1 VMSAv8-64 page table.
pub struct S1PageTable {
    /// Root address.
    pub root: PAddrExec,
    /// Frames allocated for page table.
    pub frames: Set<FrameExec>,
}

impl S1PageTable {
    /// Physical address of the root page table.
    pub open spec fn root(self) -> u64 {
        0
    }

    /// Read value at physical address `base + idx * WORD_SIZE`
    pub fn read(&self, base: u64, idx: u64) -> (res: u64) {
        0
    }

    /// Write `value` to physical address `base + idx * WORD_SIZE`
    pub fn write(&mut self, base: u64, idx: u64, value: u64) {
        // TODO: write to memory
    }

    /// Allocate a new physical frame.
    pub open spec fn alloc(self, size: FrameSize) -> (frame: Frame) {
        // TODO: allocate a new frame
        Frame {
            base: PAddr(0),
            size,
            attr: FrameAttr {
                readable: true,
                writable: true,
                executable: true,
                user_accessible: true,
            },
        }
    }

    /// Deallocate a physical frame.
    pub fn dealloc(&mut self, frame: Frame) {
        // TODO: deallocate a frame
    }

    pub open spec fn frame_view(self, frame: Frame) -> Seq<nat>;

    /// Specification of read operation.
    pub open spec fn spec_read(&self, base: u64, addr: u64) -> u64 {
        0
    }

    /// Interpret as mappings.
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
        match self.walk_level(addr, 4, self.root(), true, false, false) {
            Some(reached) => {
                &&& reached.base == frame.base
                &&& reached.size == frame.size
                &&& reached.attr == frame.attr
            },
            None => false,
        }
    }

    /// Recursive helper for page table walk.
    pub closed spec fn walk_level(
        self,
        addr: u64,
        level: nat,
        table_addr: u64,
        user_ok: bool,
        uxn_accum: bool,
        pxn_accum: bool,
    ) -> Option<Frame>
        decreases level,
    {
        if level == 0 {
            None
        } else {
            let level_shift = 39 - level * 9;
            let index = (addr >> level_shift) & 0x1FF;
            let pte = PTEntry(self.spec_read(table_addr, index))@;
            match pte {
                GhostPTEntry::Table(desc) => {
                    let new_user_ok = user_ok && desc.ap_user;
                    let new_uxn = uxn_accum || desc.uxn;
                    let new_pxn = pxn_accum || desc.pxn;
                    let next_table = desc.addr << 12;
                    self.walk_level(
                        addr,
                        (level - 1) as nat,
                        next_table,
                        new_user_ok,
                        new_uxn,
                        new_pxn,
                    )
                },
                GhostPTEntry::Page(page_desc) => {
                    if level > 3 && page_desc.non_block {
                        None  // Block must be at level 1-3, page only at level 1

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
                GhostPTEntry::Empty => None,
            }
        }
    }

    /// Compute physical address and flags for the reached frame.
    spec fn compute_frame(
        entry: GhostPageDescriptor,
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
}

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
    /// Execute Never (XN)
    pub xn: bool,
    /// Contiguous bit hint
    pub contiguous: bool,
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

/// Concrete page table entry, wrapping a 64-bit value.
pub struct PTEntry(pub u64);

impl PTEntry {
    /// Maps the concrete page table entry to its abstract representation.
    ///
    /// # Returns
    /// - `GhostPTEntry::Table` if the entry is a valid table descriptor.
    /// - `GhostPTEntry::Page` if the entry is a valid page/block descriptor.
    /// - `GhostPTEntry::Empty` if the entry is invalid or empty.
    pub open spec fn view(self) -> GhostPTEntry {
        let value = self.0;
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
                        xn,
                        contiguous,
                        ns,
                    },
                )
            }
        }
    }
}

} // verus!
