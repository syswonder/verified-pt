//! Tree model of the page table.
//!
//! - `path` defines the visit path of the abstract page table tree.
//! - `node` defines the node of the abstract page table tree.
//! - `model` wraps a root node as a abstract tree model, and provides refinement proof.
mod model;
mod node;
mod path;

pub use model::PTTreeModel;
