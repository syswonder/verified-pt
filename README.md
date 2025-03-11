# Verifying hvisor Page Table

## Overview

![arch](docs/arch.svg)

## Specification

The verification of the page table implementation is structured around a **refinement-based approach**, where lower-level specifications refine higher-level abstractions. This ensures that the implementation adheres to the desired security and functional properties.

### High-Level State Machine

The high-level state machine defines the abstract behavior of the memory system, focusing on:

1. **Memory Mappings**
   - Virtual-to-physical address translations.
   - Consistency of mappings across operations.
2. **Access Permissions**
   - Read, write, and execute permissions.
   - User vs. kernel mode access control.

This specification represents the **proof target**. Our implementation running in the intended environment should refine it. This is demonstrated in part by the proof that the low-level state machine refines this specification.

```rust
/// High level (abstract) memory state.
pub struct HighLevelState {
    /// 8-byte-indexed virtual memory.
    ///
    /// We use index rather than address. Addresses that are not aligned to 8-byte boundaries
    /// should not be used to access a value, while indexes don't face this issue.
    pub mem: Map<VIdx, nat>,
    /// Mappings from virtual address to physical frames.
    ///
    /// The key must be the base address of a virtual page i.e. virtual range [`key`, `key + frame.size`)
    /// must be mapped to the same physical frame.
    pub mappings: Map<VAddr, Frame>,
    /// Constants.
    pub constants: HighLevelConstants,
}
```

### Low-level State Machine

The low-level state machine bridges the gap between the high-level specification and the concrete implementation.

```rust
/// Low-level Memory State, which includes
///
/// - Common memory: Memory used by the OS and applications.
/// - Page table: Stage 1 page table.
/// - TLB: Translation Lookaside Buffer.
pub struct LowLevelState {
    /// 8-byte-indexed physical memory.
    pub mem: Seq<nat>,
    /// Page table.
    pub pt: S1PageTable,
    /// Translation Lookaside Buffer.
    pub tlb: Map<VAddr, Frame>,
}
```

### Refinement Relationship

The **refinement relationship** between the low-level state machine and the high-level specification ensures that:

1. Every valid low-level state transition corresponds to a valid high-level state transition.
2. The page table operations maintain the invariants defined in the low-level specification.

This refinement is proven through **simulation relations** and **invariant preservation** across the layers.
