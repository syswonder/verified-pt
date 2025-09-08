//! Provides page table management functions for different architectures.
pub mod easy;

use crate::common::{frame::MemAttr, PagingResult};

/// Page Table API.
pub trait PageTableApi {
    /// Creates an empty page table.
    fn new() -> Self;

    /// Returns the root page table address.
    fn root(&self) -> usize;

    /// Maps a virtual address to a physical address.
    fn map(&mut self, vaddr: usize, paddr: usize, size: usize, attr: MemAttr) -> PagingResult;

    /// Unmaps a virtual address.
    fn unmap(&mut self, vaddr: usize) -> PagingResult;

    /// Given a virtual address, returns the virtual base addree, physical address,
    /// frame size, and the attributes of the mapping.
    fn query(&self, vaddr: usize) -> PagingResult<(usize, usize, usize, MemAttr)>;
}
