//! Defination of abstract memory state and functions.

use vstd::prelude::*;

use super::s1pt::page_table_walk;

verus! {

/// Represents a physical memory frame (Page or Block).
pub struct Frame {
    /// The base address of the frame.
    pub base: u64,
    /// The size of the frame in bytes.
    pub size: FrameSize,
    /// The attributes of the frame.
    pub attr: FrameAttr,
}

/// Page & Block size supported by VMSA-v8.
pub enum FrameSize {
    /// 4 KiB
    Size4K,
    /// 2 MiB
    Size2M,
    /// 1 GiB
    Size1G,
}

impl FrameSize {
    pub open spec fn as_u64(self) -> u64 {
        match self {
            FrameSize::Size4K => 0x1000,
            FrameSize::Size2M => 0x200000,
            FrameSize::Size1G => 0x40000000,
        }
    }
}

/// Frame attributes. Defination consistent with `hvisor::memory::MemFlags`.
#[derive(PartialEq, Eq)]
pub struct FrameAttr {
    /// Whether the memory is readable.
    pub readable: bool,
    /// Whether the memory is writable.
    pub writable: bool,
    /// Whether the memory is executable.
    pub executable: bool,
    /// Whether the memory is user accessible.
    pub user_accessible: bool,
}

/// Memory where page table is stored.
pub struct PageTableMem {
    // TODO: fields
}

impl PageTableMem {
    pub fn new() -> Self {
        Self {  }
    }

    /// Physical address of the root page table.
    pub open spec fn root(self) -> u64 {
        0
    }

    /// Read value at physical address `base + idx * WORD_SIZE`
    pub fn read(&self, base: u64, idx: u64) -> (res: u64) {
        0
    }

    /// Write `value` to physical address `base + idx * WORD_SIZE`
    pub fn write(&mut self, base: u64, idx: u64, value: u64) {
        // TODO: write to memory
    }

    /// Allocate a new physical frame.
    pub fn alloc(&mut self, size: FrameSize) -> (frame: Frame) {
        // TODO: allocate a new frame
        Frame {
            base: 0,
            size: size,
            attr: FrameAttr {
                readable: true,
                writable: true,
                executable: true,
                user_accessible: true,
            },
        }
    }

    /// Deallocate a physical frame.
    pub fn dealloc(&mut self, frame: Frame) {
        // TODO: deallocate a frame
    }

    /// Specification of read operation.
    pub open spec fn spec_read(&self, addr: u64) -> u64 {
        // TODO: read from memory
        0
    }
}

/// OS-level Memory State, which includes
///
/// - Common memory: Memory used by the OS and applications.
/// - Page table memory: Memory used to store page tables.
/// - TLB: Translation Lookaside Buffer.
/// 
/// OS-level memory state is the operand of the OS memory state machine. The memory state
/// machine specifies the behavior of the memory management unit. These specifications are
/// composed of the following parts:
/// 
/// - Hardware. This level specifies the behavior of the memory management unit.
///   The hardware behavior must be a refinement of the specification.
/// 
/// - Page table. Describing the page table functions’ behavior as a state machine
///   operating on an abstract view of the page table.
/// 
/// - OS. The highest level of memory state transition specification, which integrates
///   the hardware level and the page table level, and describeschow the whole memory 
///   system behaves.
/// 
/// Specifications are defined in corresponding modules.
pub struct OSMemoryState {
    /// Common memory.
    pub mem: Seq<nat>,
    /// Page table memory.
    pub pt_mem: PageTableMem,
    /// TLB.
    pub tlb: Map<nat, Frame>,
}

impl OSMemoryState {
    /// Initial memory state.
    ///
    /// The initial state must satisfy the specification.
    pub open spec fn init(self) -> bool {
        &&& self.tlb.dom() === Set::empty()
        &&& serialize_pt_mem(self.pt_mem) === Map::empty()
    }
}

pub spec const MAX_BASE: nat = 0x8000_0000;

/// Serialize the page table memory to a page map.
pub open spec fn serialize_pt_mem(pt_mem: PageTableMem) -> Map<nat, Frame> {
    Map::new(
        |addr: nat|
            addr < MAX_BASE && exists|frame: Frame| #[trigger]
                page_table_walk(pt_mem, addr as u64, frame),
        |addr: nat| choose|pte: Frame| #[trigger] page_table_walk(pt_mem, addr as u64, pte),
    )
}

} // verus!
