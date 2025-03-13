# Verifying hvisor Page Table

Proof Target: [hvisor](https://github.com/syswonder/hvisor)

## Overview

![arch](docs/arch.svg)

## Specification

The verification of the page table implementation follows a **refinement-based approach**, where lower-level specifications refine higher-level abstractions. This ensures the implementation satisfies both security and functional requirements.

### High-Level State Machine

The high-level state machine defines the abstract behavior of the memory system, focusing on two key aspects:

1. **Memory Mappings**
   - Virtual-to-physical address translations.
   - Consistency of mappings across operations.
2. **Access Permissions**
   - Control over read, write, and execute permissions.
   - Enforcement of user versus kernel mode restrictions.

This specification serves as the **proof target**. The page table implementation must refine this abstract model to demonstrate correctness. The refinement proof confirms that the low-level state machine aligns with this specification.

```rust
/// Abstract memory state for the high-level model.
pub struct HighLevelState {
    /// 8-byte-indexed virtual memory.
    /// Using indexes instead of raw addresses avoids misalignment issues.
    pub mem: Map<VIdx, nat>,
    /// Mappings from virtual addresses to physical frames.
    /// The key must be the base address of a virtual page, ensuring
    /// the entire range maps to a single physical frame.
    pub mappings: Map<VAddr, Frame>,
    /// Constants defined for the high-level model.
    pub constants: HighLevelConstants,
}
```

### Low-Level State Machine

The low-level state machine provides a more concrete abstraction of the memory management module, acting as a bridge between the implementation and the high-level specification.

The verification assumes that hardware behavior refines the hardware specification. By proving the page table implementation refines the page table specification, we can conclude that the combined system (hardware + hypervisor) refines the low-level specification and, in turn, the high-level specification.

```rust
/// Low-level memory state, including:
///
/// - Common memory: Used by the OS and applications.
/// - Page table: Stage 1 page table.
/// - TLB: Translation Lookaside Buffer.
pub struct LowLevelState {
    /// 8-byte-indexed physical memory.
    pub mem: Seq<nat>,
    /// Stage 1 page table.
    pub pt: S1PageTable,
    /// Translation Lookaside Buffer.
    pub tlb: Map<VAddr, Frame>,
}
```

#### Hardware Specification

This module defines the abstract hardware state and its transition behaviors during memory operations. The hardware state includes:

- **Physical memory**
- **Page table**
- **Translation Lookaside Buffer (TLB)**

The module specifies hardware behavior during memory translations, TLB management, and page table updates.

**Assumption:** The hardware behavior refines the hardware specification, ensuring correctness in memory translations. This specification underpins the entire verification process.

```rust
/// Abstract state managed by hardware.
pub struct HardwareState {
    /// 8-byte-indexed physical memory.
    pub mem: Seq<nat>,
    /// Page table.
    pub pt: S1PageTable,
    /// Translation Lookaside Buffer.
    pub tlb: Map<VAddr, Frame>,
}
```

#### Page Table Specification

The page table specification defines the **proof target** for the page table implementation. Meeting this specification, alongside the hardware and OS assumptions, ensures the system refines the low-level specification.

Importantly, this module itself is **not trusted**; it is part of the proof rather than a trusted base.

```rust
/// Abstract state managed by the page table.
pub struct PageTableState {
    /// Mappings from virtual address to physical frames.
    pub mappings: Map<VAddr, Frame>,
    /// Page table constants.
    pub constants: PTConstants,
}

/// Page table config constants.
pub struct PTConstants {
    /// Physical memory size (in bytes).
    pub pmem_size: nat,
}
```

### Refinement Relationship

The **refinement relationship** between the low-level state machine and the high-level specification ensures:

1. Every valid low-level state transition corresponds to a valid high-level state transition.
2. Page table operations maintain the invariants defined in the low-level specification.

This relationship is established through **simulation relations** and **invariant preservation** across the layers.

## Implementation & Proof

### Page Table Interface

The **Page Table Interface** defines the contract that any concrete page table implementation must follow to ensure correctness. This interface outlines:

- **Invariants**: Conditions that must hold throughout the page table's lifetime to maintain consistency.
- **View**: An abstraction that maps the concrete implementation to the abstract `PageTableState`.
- **Operations**: The `map`, `unmap`, and `query` methods, each with well-defined preconditions and postconditions.

To verify correctness, the implementation must:

1. **Preserve Invariants**: Demonstrate that all operations uphold the defined invariants.
2. **Establish Initial Conditions**: Prove that the system's initialization state satisfies the required conditions.
3. **Prove Refinement**: Ensure that the concrete implementation refines the abstract state transitions defined in `PageTableState`.

By verifying these conditions and combining them with hardware and system assumptions, we can conclude that the overall system refines both the low-level and high-level specifications.

```rust
/// Page table must implement the `PageTableInterface` and satisfy the specification.
pub trait PageTableInterface where Self: Sized {
    /// Get abstract page table state.
    spec fn view(self) -> PageTableState;

    /// Specify the invariants that must be implied at initial state and preseved 
    /// after each operation.
    spec fn invariants(self) -> bool;

    /// The assumptions we made about the hardware and the remaining system implies 
    /// `self@.init()` at the system initialization.
    ///
    /// Implementation must prove that the invariants are satisfied at this initial state.
    proof fn init_implies_invariants(self)
        requires
            self@.init(),
        ensures
            self.invariants(),
    ;

    /// **EXEC** Map a virtual address to a physical frame.
    fn map(&mut self, vaddr: VAddrExec, frame: FrameExec) -> (result: Result<(), ()>)
        requires
            old(self).invariants(),
            old(self)@.map_pre(vaddr@, frame@),
        ensures
            self.invariants(),
            PageTableState::map(old(self)@, self@, MapOp { vaddr: vaddr@, frame: frame@, result }),
    ;

    /// **EXEC** Unmap a virtual address.
    fn unmap(&mut self, vaddr: VAddrExec) -> (result: Result<(), ()>)
        requires
            old(self).invariants(),
            old(self)@.unmap_pre(vaddr@),
        ensures
            self.invariants(),
            PageTableState::unmap(old(self)@, self@, UnmapOp { vaddr: vaddr@, result }),
    ;

    /// **EXEC** Query a virtual address, return the mapped physical frame.
    fn query(&mut self, vaddr: VAddrExec) -> (result: Result<(VAddrExec, FrameExec), ()>)
        requires
            old(self).invariants(),
            old(self)@.query_pre(vaddr@),
        ensures
            self.invariants(),
            PageTableState::query(
                old(self)@,
                self@,
                QueryOp {
                    vaddr: vaddr@,
                    result: match result {
                        Ok((vaddr, frame)) => Ok((vaddr@, frame@)),
                        Err(()) => Err(()),
                    },
                },
            ),
    ;
}
```