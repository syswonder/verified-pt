use crate::common::{
    addr::{PAddr, PAddrExec},
    frame::MemAttr,
};
use vstd::prelude::*;

verus! {

/// A ghost page table entry type.
pub ghost struct GhostPTE {
    /// The physical address mapped by this entry.
    pub addr: PAddrExec,
    /// The attributes of this entry.
    pub attr: MemAttr,
    /// Whether this entry maps to a huge frame.
    pub huge: bool,
    /// Whether this entry is valid.
    pub valid: bool,
}

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
    ;

    /// Construct an empty entry.
    fn empty() -> (pte: Self)
        ensures
            pte.spec_valid() == false,
    ;

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
            self.spec_to_u64() == res,
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
}

} // verus!
