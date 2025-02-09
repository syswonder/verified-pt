use vstd::prelude::*;

verus! {

pub struct PageTableMem {}

impl PageTableMem {
    pub fn new() -> Self {
        Self {  }
    }

    pub open spec fn root(self) -> u64 {
        0
    }

    pub open spec fn read(&self, addr: u64) -> u64 {
        // TODO: read from memory
        0
    }

    pub fn write(&self, addr: u64, data: u64) {
        // TODO: write to memory
    }
}

} // verus!
