#![allow(unused)]
#![no_std]

use vstd::prelude::*;

pub mod arch;
pub mod common;
pub mod imp;
pub mod spec;

#[cfg(feature = "usermode")]
pub mod usermode;

pub use arch::PageTable;
pub mod memory {
    pub use crate::spec::memory::{PageTableMem, PageTableMemExec, Table};
}
pub mod utils {
    pub use crate::common::{
        addr::{PAddrExec, VAddrExec},
        arch::{PTArchExec, PTArchLevelExec},
        frame::{MemAttr, FrameSize},
        pte::{ExecPTE, GhostPTE},
        PagingResult,
    };
}
#[cfg(feature = "aarch64")]
pub mod aarch64 {
    pub use crate::arch::aarch64::*;
}

verus! {

global layout usize is size == 8;

} // verus!
/// Although the project is a library, Verus requires a main function to run the verification.
fn main() {}
