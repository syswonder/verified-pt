//! Concrete page table implementation.
use vstd::prelude::*;

use super::tree::PTTreeModel;
use crate::spec::{addr::VAddrExec, frame::FrameExec};

verus! {

/// An executable page table.
pub struct PageTable {
    /// Page table tree model.
    tree_model: Ghost<PTTreeModel>,
}

impl PageTable {
    fn map(&mut self, vbase: VAddrExec, frame: FrameExec) -> (res: Result<(), ()>) {
        Err(())
    }
}

} // verus!
