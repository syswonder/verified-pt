use vstd::prelude::*;

mod imp;
mod spec;
mod common;

verus! {
    global layout usize is size == 8;
}

/// Although the project is a library, Verus requires a main function to run the verification.
fn main() {}
