#![feature(lazy_cell)]

use vstd::prelude::*;

mod imp;
mod spec;
mod common;
mod arch;

verus! {
    global layout usize is size == 8;
}

/// Although the project is a library, Verus requires a main function to run the verification.
fn main() {
    println!("Running Test...");
    test();
}

fn test() {
    use arch::easy::EasyPageTable;
    use arch::PageTableApi;
    use common::frame::MemAttr;

    let mut pt = EasyPageTable::new();
    println!("PageTable Inited");
    let r1 = pt.map(0x1000, 0x2000, 4096, MemAttr::default());
    assert!(r1.is_ok());
    println!("map ok");
    let r2 = pt.query(0x1020);
    assert!(r2.is_ok());
    assert!(r2.unwrap() == (0x1000, 0x2000, 4096, MemAttr::default()));
    println!("query_after_map ok");
    let r3 = pt.unmap(0x1000);
    assert!(r3.is_ok());
    println!("unmap ok");
    let r4 = pt.query(0x1010);
    assert!(r4.is_err());
    println!("query_after_unmap ok ");
}