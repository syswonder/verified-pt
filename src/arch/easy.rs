//! A toy page table entry implementation for testing.
use vstd::prelude::*;

use crate::common::{
    addr::{PAddr, PAddrExec},
    frame::MemAttr,
    pte::{ExecPTE, GhostPTE},
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

/// The 3-level easy architecture is specified as follows:
///
/// | Level | Index into PT | Entry Num |  Entry Type  | Frame Size |
/// |-------|---------------|-----------|--------------|------------|
/// | 1     | 38:30         | 512       | Table/Block  | 1G         |
/// | 2     | 29:21         | 512       | Table/Block  | 2M         |
/// | 3     | 20:12         | 512       | Page         | 4K         |
pub fn easy_3level_arch() -> PTArchExec {
    PTArchExec(
        [
            PTArchLevelExec { entry_count: 512, frame_size: FrameSize::Size1G },
            PTArchLevelExec { entry_count: 512, frame_size: FrameSize::Size2M },
            PTArchLevelExec { entry_count: 512, frame_size: FrameSize::Size4K },
        ].to_vec(),
    )
}

/// Page table of easy architecture.
pub type EasyPageTable<M> = PageTable<M, EasyGhostPTE, EasyExecPTE>;

} // verus!
