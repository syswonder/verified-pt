//! Provides page table management functions for different architectures.
use crate::{
    common::{
        addr::{PAddrExec, VAddrExec},
        arch::PTArchExec,
        frame::{FrameExec, FrameSize, MemAttr},
        pte::{ExecPTE, GhostPTE},
        PagingResult,
    },
    imp::{interface::PTConstantsExec, paging::pt_exec::PageTableExec},
    spec::memory::PageTableMemExec,
};
use core::marker::PhantomData;

#[cfg(feature = "aarch64")]
pub mod aarch64;
#[cfg(feature = "easy")]
pub mod easy;

/// A wrapper of `PageTableExec` for easier usage.
///
/// Provides a simple interface for `map`, `unmap`, `query`, and `protect` functions.
pub struct PageTable<M, G, E>(PageTableExec<M, G, E>)
where
    M: PageTableMemExec,
    G: GhostPTE,
    E: ExecPTE<G>;

impl<M, G, E> PageTable<M, G, E>
where
    M: PageTableMemExec,
    G: GhostPTE,
    E: ExecPTE<G>,
{
    /// Creates an empty page table.
    pub fn new(arch: PTArchExec, pmem_lb: usize, pmem_ub: usize) -> Self {
        Self(PageTableExec {
            pt_mem: M::new_init(arch.clone()),
            constants: PTConstantsExec {
                arch,
                pmem_lb: PAddrExec(pmem_lb),
                pmem_ub: PAddrExec(pmem_ub),
            },
            _phantom: PhantomData,
        })
    }

    /// Returns the root page table address.
    pub fn root(&self) -> usize {
        self.0.pt_mem.root().0
    }

    /// Returns the page table architecture.
    pub fn arch(&self) -> PTArchExec {
        self.0.constants.arch.clone()
    }

    /// Maps a virtual address to a physical address.
    pub fn map(
        &mut self,
        vbase: usize,
        paddr: usize,
        size: FrameSize,
        attr: MemAttr,
    ) -> PagingResult {
        self.0.map(
            VAddrExec(vbase),
            FrameExec {
                base: PAddrExec(paddr),
                size,
                attr,
            },
        )
    }

    /// Unmaps a virtual address.
    pub fn unmap(&mut self, vbase: usize) -> PagingResult {
        self.0.unmap(VAddrExec(vbase))
    }

    /// Given a virtual address, returns the virtual base addree, physical address,
    /// frame size, and the attributes of the mapping.
    pub fn query(&self, vaddr: usize) -> PagingResult<(usize, usize, FrameSize, MemAttr)> {
        self.0
            .query(VAddrExec(vaddr))
            .map(|(vbase, frame)| (vbase.0, frame.base.0, frame.size, frame.attr))
    }

    /// Updates the attributes of a mapping. Implements as unmap + map.
    pub fn protect(&mut self, vbase: usize, attr: MemAttr) -> PagingResult {
        let (vbase, frame) = self.0.query(VAddrExec(vbase))?;
        self.0.unmap(vbase)?;
        self.0.map(
            vbase,
            FrameExec {
                base: frame.base,
                size: frame.size,
                attr,
            },
        )
    }
}
