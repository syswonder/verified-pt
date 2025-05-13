//! Specification of the page table module, consisting of
//!
//! - High-level. Abstracts the whole memory management module, acts as the proof target.
//! - Memory. Model and specification of physical memery, page table memory, and TLB.
//! - Hardware. Specifies the harware MMU behavior.
//! - Page table. Defines the implementation target of the page table.
//! - Low-level. Acts as a bridge between the implementation and the high-level specification.
pub mod hardware;
pub mod high_level;
pub mod low_level;
pub mod memory;
pub mod pt_spec;
