//! Page table memory implementation.
//!
//! Page table memory is a memory region that stores page tables, allocated by the memory allocator.
//! Hardware access page table memory and performs page table walks to translate VA to PA.
//! To satisfies the specification defined in `spec::hardware`, the correctness of the memory allocator
//! and raw memory access is assumed.
//!
//! Page table memory is designed to be architecture independent, but yet only supports VMSAv8-64.
use vstd::{pervasive::unreached, prelude::*};

use super::arch::{lemma_vmsav8_4k_arch_valid, VMSAV8_4K_ARCH};
use crate::{
    common::{addr::PAddrExec, arch::PTArch, frame::FrameSize},
    spec::memory::{PageTableMem, Table},
};

verus! {

/// Create an empty page table memory that only contains root table.
pub fn new_vmsav8_4k(root: PAddrExec) -> (res: Self)
    ensures
        res@.arch == VMSAV8_4K_ARCH,
        res@.init(),
{
    let root_table = TableExec { base: root, size: FrameSize::Size4K, level: Ghost(0) };
    let res = Self { tables: vec![root_table], arch: Ghost(VMSAV8_4K_ARCH) };
    proof {
        lemma_vmsav8_4k_arch_valid();
        // Assume init value of page table memory
        assume(res@.table_view(res@.root()) == seq![0u64; res@.arch.entry_count(0)]);
    }
    res
}

} // verus!
