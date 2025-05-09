//! Basic structures and functions used by the other modules.
use vstd::prelude::*;

pub mod addr;
pub mod arch;
pub mod frame;

verus! {

/// Result type returned by paging operations (map, unmap, query).
pub type PagingResult<T = ()> = Result<T, ()>;

/// Result type returned by memory operations (read, write).
pub enum MemoryResult<T> {
    /// Success.
    Ok(T),
    /// Page fault.
    PageFault,
}

} // verus!
