# Verified Page Table Implementation

An arch-independent page table implementation, formally verified by [Verus](https://github.com/verus-lang/verus).

Used by [hvisor](https://github.com/syswonder/hvisor), a lightweight Type-I Hypervisor, to provide memory isolation for guest VMs.

## Usage

### Prerequisites

Add the following to your `Cargo.toml`:

```toml
[dependencies]
verified-pt = { git = "https://github.com/syswonder/verified-pt.git" }
```

If you want to support VMSAv8-64 architecture, enable the `aarch64` feature:

```toml
[dependencies]
verified-pt = { git = "https://github.com/syswonder/verified-pt.git", features = ["aarch64"] }
```

### Use the Page Table

1. Implement the page table memory: 
   
   Page table memory stores page tables and must support basic operations (read, write, allocate). Implement the PageTableMem trait for your memory type.

```rust
use verified_pt::memory::PageTableMem;

impl PageTableMem for YourMemoryType {
    // Implement required methods here
}
```

2. Construct the page table.

```rust
use verified_pt::aarch64::{Aarch64PageTable, vmsav8_4k_4level_arch};

let mut page_table = Aarch64PageTable::<YourMemoryType>::new(vmsav8_4k_4level_arch, 0x0, 0x80000000);
```

3. Use page table operations.

```rust
use verified_pt::utils::{FrameSize, MemAttr};

// Map a virtual address to a physical address
page_table.map(0x0, 0x10000000, FrameSize::Size4K, MemAttr::default()).unwrap();
```

### Run verification

If you want to run the verification, you need to install the Verus verifier. See [Verus installation guide](https://github.com/verus-lang/verus/blob/master/INSTALL.md) for more details.

Then, run the following command in the project root directory:

```bash
verus src/lib.rs
```

Add more options for more detailed output (use `verus --help` for more information).

## Proof Structure

### Overview

The following figure illustrates the proof architecture for the formal verification of page tables.

<img src="docs/arch.svg" alt="arch" style="zoom:80%;" />

- **High-Level State Machine**: The final proof target, specifying the abstract behavior of the memory system.
- **Low-Level State Machine**: A concrete abstraction of the memory management module, bridging the implementation and the high-level model.
  - **Hardware Spec**: Assumptions about underlying system and hardware behavior, trusted as the proof base.
  - **Page Table Spec**: Defines requirements for the concrete page table implementation.
- **Page Table Tree Model**: Helper models for implementation refinement proofs.
- **Page Table Implementation**: Concrete page table implementation in executable Rust code.

### Specification

The verification follows a **refinement-based approach**, ensuring lower-level specifications refine higher-level abstractions. This guarantees the implementation satisfies both security and functional requirements.

#### High-Level State Machine

The high-level state machine defines abstract memory system behavior, focusing on:

- **Memory Mappings**: Virtual-to-physical address translations.
- **Access Permissions**: Control over read, write, and execute permissions.

This specification serves as the **proof target**, requiring the memory system to refine this model.

#### Low-Level State Machine

The low-level state machine bridges the implementation and high-level specification. It assumes hardware behavior refines the hardware specification. By proving the page table implementation refines its specification, we conclude the combined system (hardware + hypervisor) refines both low-level and high-level specifications.

#### Hardware Specification

Defines abstract hardware state and transitions during memory operations, including:
- **Physical memory**
- **Page table**
- **Translation Lookaside Buffer (TLB)**

**Assumption**: Hardware behavior refines this specification, ensuring correct memory translations. This forms the trusted base for verification.

#### Page Table Specification

Defines the specification for the page table implementation. Combined with hardware assumptions, meeting this specification ensures system refinement. 

#### Refinement Relationship

The **refinement relationship** between low-level and high-level specifications ensures:
1. Valid low-level transitions correspond to valid high-level transitions.
2. Page table operations preserve invariants in the low-level specification.

This is established through **operation abstraction** and **invariant preservation** across layers.

### Implementation & Proof

#### Page Table Implementation

The page table implementation is a Rust module that defines the page table management functions. It is **verified** against the page table specification.

Implementation is wrapped in struct `arch::PageTable`, which provides methods for mapping, unmapping, and querying memory mappings.

```rust
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
        ...
    }

    /// Maps a virtual address to a physical address.
    pub fn map(
        &mut self,
        vbase: usize,
        paddr: usize,
        size: FrameSize,
        attr: MemAttr,
    ) -> PagingResult {
        ...
    }

    /// Unmaps a virtual address.
    pub fn unmap(&mut self, vbase: usize) -> PagingResult {
        ...
    }

    /// Given a virtual address, returns the virtual base addree, physical address,
    /// frame size, and the attributes of the mapping.
    pub fn query(
      &self, 
      vaddr: usize,
    ) -> PagingResult<(usize, usize, FrameSize, MemAttr)> {
        ...
    }
}
```

Page table entries are represented as traits (`GhostPTE` for spec-mode and `ExecPTE` for exec-mode), allowing architecture-specific implementations (e.g., x86_64, RISC-V) to conform to a common interface.

VMSAv8-64 architecture is currently supported by implementing the traits (feature `aarch64`). 

#### Low-Level to High-Level Refinement

A refinement proof ensures consistency between low-level implementation and high-level specification. The following figure illustrates the proof idea.

![](docs/ll_refine_hl.svg)

#### Page Table Tree Model 

The page table tree model is a helper model for proving the correctness of the page table implementation. 
It abstracts the page table as a tree structure, where each node represents a leaf entry or a pointer to a child page table. This model provides a more detailed abstraction of the page table structure and operations, facilitating the refinement proof.

![](docs/tree.svg)

The refinement proof between the page table tree model and the low-level specification is conducted in the `imp::tree` module.

#### Implementation Refinement Proof

The page table implementation is refined against the page table tree model, ensuring the implementation satisfies the low-level specification. This is done in the `imp::pt` module.

## Related Works

- [Verified Paging for x86-64 in Rust](https://github.com/matthias-brun/verified-paging-for-x86-64-in-rust)
- [vostd](https://github.com/asterinas/vostd)
