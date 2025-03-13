# Verifying hvisor Page Table

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

#### Page Table Specification

The page table specification defines the **proof target** for the page table implementation. Meeting this specification, alongside the hardware and OS assumptions, ensures the system refines the low-level specification.

Importantly, this module itself is **not trusted**; it is part of the proof rather than a trusted base.

### Refinement Relationship

The **refinement relationship** between the low-level state machine and the high-level specification ensures:

1. Every valid low-level state transition corresponds to a valid high-level state transition.
2. Page table operations maintain the invariants defined in the low-level specification.

This relationship is established through **simulation relations** and **invariant preservation** across the layers.

