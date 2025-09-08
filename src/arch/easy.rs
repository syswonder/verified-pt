//! A toy page table implementation for testing.
use vstd::prelude::*;

use super::PageTableApi;
use crate::imp::paging::pt_exec::PageTableExec;
use crate::{
    common::{
        addr::{PAddr, PAddrExec, VAddrExec},
        arch::{PTArchExec, PTArchLevelExec},
        frame::{FrameExec, FrameSize, MemAttr},
        pte::{ExecPTE, GhostPTE},
        PagingResult,
    },
    spec::memory::PageTableMemExec,
    imp::interface::PTConstantsExec,
};

verus! {

/// Easy ghost PTE.
///
/// |addr: 63-12||padding: 11-7||attr: 6-2||huge: 1||valid: 0|
pub struct EasyGhostPTE {
    pub addr: PAddr,
    pub attr: MemAttr,
    pub huge: bool,
    pub valid: bool,
}

impl GhostPTE for EasyGhostPTE {
    open spec fn new(addr: PAddr, attr: MemAttr, huge: bool) -> Self {
        Self { addr, attr, huge, valid: true }
    }

    open spec fn empty() -> Self {
        Self { addr: PAddr(0nat), attr: MemAttr::spec_default(), huge: false, valid: false }
    }

    open spec fn addr(self) -> PAddr {
        self.addr
    }

    open spec fn attr(self) -> MemAttr {
        self.attr
    }

    open spec fn valid(self) -> bool {
        self.valid
    }

    open spec fn huge(self) -> bool {
        self.huge
    }

    open spec fn from_u64(val: u64) -> Self {
        let addr = PAddr((val >> 12 << 12) as nat);
        let readable = val & 0b100 != 0;
        let writable = val & 0b1000 != 0;
        let executable = val & 0b10000 != 0;
        let user_accessible = val & 0b100000 != 0;
        let device = val & 0b1000000 != 0;
        let huge = val & 0b10 != 0;
        let valid = val & 0b1 != 0;
        Self {
            addr,
            attr: MemAttr { readable, writable, executable, user_accessible, device },
            huge,
            valid,
        }
    }

    open spec fn to_u64(self) -> u64 {
        let a = self.addr.0 as u64 >> 12 << 12;
        let b = if self.attr.readable {
            0b100
        } else {
            0
        };
        let c = if self.attr.writable {
            0b1000
        } else {
            0
        };
        let d = if self.attr.executable {
            0b10000
        } else {
            0
        };
        let e = if self.attr.user_accessible {
            0b100000
        } else {
            0
        };
        let f = if self.attr.device {
            0b1000000
        } else {
            0
        };
        let g = if self.huge {
            0b10
        } else {
            0
        };
        let h = if self.valid {
            0b1
        } else {
            0
        };
        a | b | c | d | e | f | g | h
    }

    proof fn lemma_empty_invalid() {
    }

    proof fn lemma_from_0_invalid() {
        admit()
    }

    proof fn lemma_from_to_u64_inverse(val: u64) {
        admit()
    }

    proof fn lemma_new_keeps_value(addr: PAddr, attr: MemAttr, huge: bool) {
    }

    proof fn lemma_eq_by_u64(pte1: Self, pte2: Self) {
        admit()
    }
}

/// Easy executable PTE implementation.
///
/// |addr: 63-12||padding: 11-7||attr: 6-2||huge: 1||valid: 0|
#[derive(Clone)]
pub struct EasyExecPTE {
    pub addr: PAddrExec,
    pub attr: MemAttr,
    pub huge: bool,
    pub valid: bool,
}

impl ExecPTE<EasyGhostPTE> for EasyExecPTE {
    open spec fn view(self) -> EasyGhostPTE {
        EasyGhostPTE { addr: self.addr@, attr: self.attr, huge: self.huge, valid: self.valid }
    }

    fn new(addr: PAddrExec, attr: MemAttr, huge: bool) -> Self {
        Self { addr, attr, huge, valid: true }
    }

    fn empty() -> Self {
        Self { addr: PAddrExec(0), attr: MemAttr::default(), huge: false, valid: false }
    }

    fn addr(&self) -> (res: PAddrExec) {
        self.addr
    }

    fn attr(&self) -> (res: MemAttr) {
        self.attr
    }

    fn huge(&self) -> (res: bool) {
        self.huge
    }

    fn valid(&self) -> (res: bool) {
        self.valid
    }

    fn from_u64(val: u64) -> (pte: Self) {
        let addr = PAddrExec((val >> 12 << 12) as usize);
        let readable = val & 0b100 != 0;
        let writable = val & 0b1000 != 0;
        let executable = val & 0b10000 != 0;
        let user_accessible = val & 0b100000 != 0;
        let device = val & 0b1000000 != 0;
        let huge = val & 0b10 != 0;
        let valid = val & 0b1 != 0;
        Self {
            addr,
            attr: MemAttr { readable, writable, executable, user_accessible, device },
            huge,
            valid,
        }
    }

    fn to_u64(&self) -> (res: u64) {
        let a = self.addr.0 as u64 >> 12 << 12;
        let b = if self.attr.readable {
            0b100
        } else {
            0
        };
        let c = if self.attr.writable {
            0b1000
        } else {
            0
        };
        let d = if self.attr.executable {
            0b10000
        } else {
            0
        };
        let e = if self.attr.user_accessible {
            0b100000
        } else {
            0
        };
        let f = if self.attr.device {
            0b1000000
        } else {
            0
        };
        let g = if self.huge {
            0b10
        } else {
            0
        };
        let h = if self.valid {
            0b1
        } else {
            0
        };
        a | b | c | d | e | f | g | h
    }
}

} // verus!

/// Easy Page Table Architecture: 3-level, each level 512 entries.
fn easy_pt_arch() -> PTArchExec {
    PTArchExec(vec![
        PTArchLevelExec {
            entry_count: 512,
            frame_size: FrameSize::Size1G,
        },
        PTArchLevelExec {
            entry_count: 512,
            frame_size: FrameSize::Size2M,
        },
        PTArchLevelExec {
            entry_count: 512,
            frame_size: FrameSize::Size4K,
        },
    ])
}

/// Physical memory lower and upper bounds.
const EASY_PMEM_LB: usize = 0b1000;
const EASY_PMEM_UB: usize = 0b100000000;

/// Easy Page Table Implementation.
/// 
/// The underlying page table memory can be any type that implements `PageTableMemExec`.
pub struct EasyPageTable<M: PageTableMemExec>(PageTableExec<M, EasyGhostPTE, EasyExecPTE>);

impl<M> PageTableApi for EasyPageTable<M> where M: PageTableMemExec {
    fn new() -> Self {
        let arch = easy_pt_arch();
        Self(PageTableExec::new(
            M::new_init(arch.clone()),
            PTConstantsExec {
                arch,
                pmem_lb: PAddrExec(EASY_PMEM_LB),
                pmem_ub: PAddrExec(EASY_PMEM_UB),
            },
        ))
    }

    fn root(&self) -> usize {
        self.0.pt_mem.root().0
    }

    fn map(&mut self, vbase: usize, paddr: usize, size: usize, attr: MemAttr) -> PagingResult {
        let size = if size == FrameSize::Size1G.as_usize() {
            FrameSize::Size1G
        } else if size == FrameSize::Size2M.as_usize() {
            FrameSize::Size2M
        } else {
            FrameSize::Size4K
        };
        self.0.map(
            VAddrExec(vbase),
            FrameExec {
                base: PAddrExec(paddr),
                size,
                attr,
            },
        )
    }

    fn unmap(&mut self, vaddr: usize) -> PagingResult {
        self.0.unmap(VAddrExec(vaddr))
    }

    fn query(&self, vaddr: usize) -> PagingResult<(usize, usize, usize, MemAttr)> {
        self.0
            .query(VAddrExec(vaddr))
            .map(|(vbase, frame)| (vbase.0, frame.base.0, frame.size.as_usize(), frame.attr))
    }
}
