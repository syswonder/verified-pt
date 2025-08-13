use crate::common::{
    addr::{PAddr, PAddrExec},
    frame::MemAttr,
};
use vstd::prelude::*;

verus! {

/// Generic interface for a page table entry.
///
/// Use preconditions and postconditions to specify the behavior of the methods.
pub trait GenericPTE: Sized + Clone {
    /// Construct from address and attributes.
    fn new(addr: PAddrExec, attr: MemAttr, huge: bool) -> (pte: Self)
        ensures
            pte.spec_addr() == addr@,
            pte.spec_attr() == attr,
            pte.spec_huge() == huge,
            pte.spec_valid(),
            pte == Self::spec_new(addr@, attr, huge),
    ;

    /// Construct from address and attributes (spec mode).
    spec fn spec_new(addr: PAddr, attr: MemAttr, huge: bool) -> Self;

    /// Construct an empty entry.
    fn empty() -> (pte: Self)
        ensures
            pte == Self::spec_empty(),
    ;

    /// Construct an empty entry (spec mode).
    spec fn spec_empty() -> Self;

    /// Parse from a u64 value.
    fn from_u64(val: u64) -> (pte: Self)
        ensures
            val == pte.spec_to_u64(),
            pte == Self::spec_from_u64(val),
    ;

    /// Parse from a u64 value (spec mode).
    spec fn spec_from_u64(val: u64) -> Self;

    /// Convert to a u64 value.
    fn to_u64(&self) -> (res: u64)
        ensures
            res == self.spec_to_u64(),
            self == Self::spec_from_u64(res),
    ;

    /// Convert to a u64 value (spec mode).
    spec fn spec_to_u64(self) -> u64;

    /// Returns the physical address mapped by this entry.
    fn addr(&self) -> (res: PAddrExec)
        ensures
            res@ == self.spec_addr(),
    ;

    /// Returns the physical address mapped by this entry (spec mode).
    spec fn spec_addr(self) -> PAddr;

    /// Returns the attributes of this entry.
    fn attr(&self) -> (res: MemAttr)
        ensures
            res == self.spec_attr(),
    ;

    /// Returns the attributes of this entry (spec mode).
    spec fn spec_attr(self) -> MemAttr;

    /// Returns whether this entry is valid.
    fn valid(&self) -> (res: bool)
        ensures
            res == self.spec_valid(),
    ;

    /// Returns whether this entry is valid (spec mode).
    spec fn spec_valid(self) -> bool;

    /// Returns whether this entry maps to a huge frame.
    ///
    /// In VMSAv8-64, the entry is called a "block descriptor".
    fn huge(&self) -> (res: bool)
        ensures
            res == self.spec_huge(),
    ;

    /// Returns whether this entry maps to a huge frame (spec mode).
    spec fn spec_huge(self) -> bool;

    /// PTE constructed by `spec_new` keeps the same value.
    broadcast proof fn lemma_spec_new_keeps_value(addr: PAddr, attr: MemAttr, huge: bool)
        ensures
            ({
                let pte = #[trigger] Self::spec_new(addr, attr, huge);
                pte.spec_valid() && pte.spec_addr() == addr && pte.spec_attr() == attr
                    && pte.spec_huge() == huge
            }),
    ;

    /// `PTE::spec_empty().spec_valid()` is false.
    broadcast proof fn lemma_empty_invalid()
        ensures
            #[trigger] Self::spec_empty().spec_valid() == false,
    ;

    /// If a page table entry has value 0, it must be invalid.
    broadcast proof fn lemma_from_0_invalid()
        ensures
            #[trigger] Self::spec_from_u64(0).spec_valid() == false,
    ;

    /// `pte1.spec_to_u64() == pte2.spec_to_u64()` implies `pte1 == pte2`.
    broadcast proof fn lemma_eq_by_u64(pte1: Self, pte2: Self)
        ensures
            #[trigger] pte1.spec_to_u64() == #[trigger] pte2.spec_to_u64() ==> pte1 == pte2,
    ;

    /// `from_u64` and `to_u64` are inverses.
    broadcast proof fn lemma_from_to_u64_inverse(val: u64)
        ensures
            #[trigger] Self::spec_from_u64(val).spec_to_u64() == val,
    ;
}

pub broadcast group group_pte_lemmas {
    GenericPTE::lemma_from_0_invalid,
    GenericPTE::lemma_empty_invalid,
    GenericPTE::lemma_eq_by_u64,
    GenericPTE::lemma_from_to_u64_inverse,
    GenericPTE::lemma_spec_new_keeps_value,
}

} // verus!
