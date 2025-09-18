#![allow(unused)]
#![no_std]

use vstd::prelude::*;

pub mod arch;
pub mod common;
pub mod imp;
pub mod spec;

#[cfg(feature = "usermode")]
pub mod usermode;

verus! {

global layout usize is size == 8;

} // verus!
/// Although the project is a library, Verus requires a main function to run the verification.
fn main() {}
