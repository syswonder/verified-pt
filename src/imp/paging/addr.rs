//! Helpers for calculating addresses and indices.
use crate::spec::{addr::VAddrExec, arch::VMSAV8_4K_ARCH};
use vstd::prelude::*;

verus! {

global layout usize is size == 8;

/// Calculate PTE index of a virtual address at a given level.
pub fn pte_index(vaddr: VAddrExec, level: usize) -> (res: usize)
    requires
        0 <= level <= 3,
    ensures
        VMSAV8_4K_ARCH.pte_index_of_va(vaddr@, level as nat) == res as nat,
{
    // Use division instead of bit shifts to avoid verus failure
    if level == 0 {
        vaddr.0 / 0x8000000000usize % 512
    } else if level == 1 {
        vaddr.0 / 0x40000000usize % 512
    } else if level == 2 {
        vaddr.0 / 0x200000usize % 512
    } else {
        vaddr.0 / 0x1000usize % 512
    }
}

} // verus!
