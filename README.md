# Formal Verification of VM Memory Isolation in Type-I Hypervisor

Proof Target: [hvisor](https://github.com/syswonder/hvisor)

## Introduction

### Memory Isolation

Ensuring VM memory isolation is crucial for the security of Type-I hypervisors. This report examines formal verification methods to validate noninterference in memory access. The following figure illustrates how a hypervisor manages VMs, each with private memory regions, alongside shared memory. Page tables enforce access controls, preventing unauthorized interference.

![](docs/isolation.svg)

By verifying structural and permission correctness in memory management, we ensure strict isolation between VMs. Using formal verification techniques, this study aims to establish provable security guarantees, reducing the risk of memory leaks and cross-VM attacks in hypervisor-based environments.

### Key Components Ensuring Memory Isolation

Two key components ensure memory isolation: the **page table** and the **memory allocator**, as shown in the following figure.

![](docs/memory.svg)

- **Page Table**: Enforces access control by ensuring a VM cannot read or write another VM’s private memory. It maps virtual addresses to physical memory while enforcing isolation policies.
- **Memory Allocator**: Ensures non-overlapping private memory regions for different VMs. It partitions memory safely, allowing controlled access to shared memory when needed.

Together, these mechanisms maintain strict isolation, preventing unauthorized access and ensuring virtualization security.

## Formal Verification of Page Table

The following figure illustrates the proof architecture for the formal verification of page tables.

![arch](docs/arch.svg)

- **High-Level State Machine**: The final proof target, specifying the abstract behavior of the memory system.
- **Low-Level State Machine**: A concrete abstraction of the memory management module, bridging the implementation and the high-level model.
  - **Hardware Spec**: Assumptions about underlying system and hardware behavior, trusted as the proof base.
  - **Page Table Spec**: Defines requirements for the concrete page table implementation.
- **Page Table Map/Tree Model**: Helper models for implementation refinement proofs.
- **Page Table Implementation**: Concrete page table implementation in executable Rust code.

## Specification

The verification follows a **refinement-based approach**, ensuring lower-level specifications refine higher-level abstractions. This guarantees the implementation satisfies both security and functional requirements.

### High-Level State Machine

The high-level state machine defines abstract memory system behavior, focusing on:
1. **Memory Mappings**:
   - Virtual-to-physical address translations.
   - Consistency of mappings across operations.
2. **Access Permissions**:
   - Control over read, write, and execute permissions.
   - Enforcement of user versus kernel mode restrictions.

This specification serves as the **proof target**, requiring the memory system to refine this model. The refinement proof confirms alignment between low-level and high-level specifications.

```rust
/// High-level (abstract) memory state.
pub struct HighLevelState {
    /// 8-byte-indexed virtual memory.
    pub mem: Map<VIdx, u64>,
    /// Mappings from virtual address to physical frames.
    pub mappings: Map<VAddr, Frame>,
    /// Constants.
    pub constants: HighLevelConstants,
}
```

### Low-Level State Machine

The low-level state machine bridges the implementation and high-level specification. It assumes hardware behavior refines the hardware specification. By proving the page table implementation refines its specification, we conclude the combined system (hardware + hypervisor) refines both low-level and high-level specifications.

```rust
/// Low-level memory state.
pub struct LowLevelState {
    /// Physical memory.
    pub mem: PhysMem,
    /// Page table.
    pub pt: PageTableMem,
    /// Translation Lookaside Buffer.
    pub tlb: TLB,
    /// Constants.
    pub constants: LowLevelConstants,
}
```

#### Hardware Specification

Defines abstract hardware state and transitions during memory operations, including:
- **Physical memory**
- **Page table**
- **Translation Lookaside Buffer (TLB)**

**Assumption**: Hardware behavior refines this specification, ensuring correct memory translations. This forms the trusted base for verification.

```rust
/// Abstract state managed by hardware.
pub struct HardwareState {
    /// Physical memory.
    pub mem: PhysMem,
    /// Page table.
    pub pt: PageTableMem,
    /// Translation Lookaside Buffer.
    pub tlb: TLB,
}
```

#### Page Table Specification

Defines the **proof target** for the page table implementation. Combined with hardware assumptions, meeting this specification ensures system refinement. Notably, this module is **not trusted**—it is part of the proof, not the trusted base.

```rust
/// Abstract state managed by the page table.
pub struct PageTableState {
    /// Mappings from virtual address to physical frames.
    pub mappings: Map<VAddr, Frame>,
    /// Page table constants.
    pub constants: PTConstants,
}

/// Page table configuration constants.
pub struct PTConstants {
    /// Physical memory size (in bytes).
    pub pmem_size: nat,
}
```

### Refinement Relationship

The **refinement relationship** between low-level and high-level specifications ensures:
1. Valid low-level transitions correspond to valid high-level transitions.
2. Page table operations preserve invariants in the low-level specification.

This is established through **simulation relations** and **invariant preservation** across layers.

## Implementation & Proof

### Low-Level to High-Level Refinement

A refinement proof ensures consistency between low-level implementation and high-level specification. The following figure illustrates the proof idea.

![](docs/ll_refine_hl.svg)

For example, the `write` operation proof involves two theorems:

```rust
/// Theorem: Low-level write preserves invariants.
proof fn ll_write_preserves_invariants(
    s1: LowLevelState,
    s2: LowLevelState,
    vaddr: VAddr,
    value: u64,
    res: Result<(), ()>,
)
    requires
        s1.invariants(),
        LowLevelState::write(s1, s2, vaddr, value, res),
    ensures
        s2.invariants(),
;

/// Theorem: Low-level write refines high-level write.
proof fn ll_write_refines_hl_write(
    s1: LowLevelState,
    s2: LowLevelState,
    vaddr: VAddr,
    value: u64,
    res: Result<(), ()>,
)
    requires
        s1.invariants(),
        LowLevelState::write(s1, s2, vaddr, value, res),
    ensures
        HighLevelState::write(s1@, s2@, vaddr, value, res),
;
```

- `ll_write_preserves_invariants` ensures invariants hold after the operation.
- `ll_write_refines_hl_write` ensures low-level operations refine high-level specifications.

Similar proofs for `read`, `map`, and `unmap` operations guarantee invariant preservation and refinement across state transitions.

### Page Table Interface

The **Page Table Interface** defines the contract for concrete implementations, requiring:
- **Invariants**: Conditions maintained throughout the page table’s lifetime.
- **View**: Abstraction mapping to the `PageTableState`.
- **Operations**: `map`, `unmap`, and `query` with pre/postconditions.

Verification requires:
1. **Invariant Preservation**: All operations uphold invariants.
2. **Initial Conditions**: System initialization satisfies invariants.
3. **Refinement Proof**: Concrete implementation refines `PageTableState` transitions.

```rust
/// Page table must implement `PageTableInterface` to ensure correctness.
pub trait PageTableInterface where Self: Sized {
    /// Get abstract page table state.
    spec fn view(self) -> PageTableState;

    /// Invariants required at initialization and preserved by operations.
    spec fn invariants(self) -> bool;

    /// Proof that invariants hold at initialization.
    proof fn init_implies_invariants(self)
        requires
            self@.init(),
        ensures
            self.invariants(),
    ;

    /// Map a virtual address to a physical frame.
    fn map(&mut self, vaddr: VAddrExec, frame: FrameExec) -> (res: Result<(), ()>)
        requires
            old(self).invariants(),
            old(self)@.map_pre(vaddr@, frame@),
        ensures
            self.invariants(),
            PageTableState::map(old(self)@, self@, vaddr@, frame@, res),
    ;

    /// Unmap a virtual address.
    fn unmap(&mut self, vaddr: VAddrExec) -> (res: Result<(), ()>)
        requires
            old(self).invariants(),
            old(self)@.unmap_pre(vaddr@),
        ensures
            self.invariants(),
            PageTableState::unmap(old(self)@, self@, vaddr@, res),
    ;

    /// Query a virtual address.
    fn query(&mut self, vaddr: VAddrExec) -> (res: Result<(VAddrExec, FrameExec), ()>)
        requires
            old(self).invariants(),
            old(self)@.query_pre(vaddr@),
        ensures
            self.invariants(),
            PageTableState::query(
                old(self)@,
                self@,
                vaddr@,
                match res {
                    Ok((vaddr, frame)) => Ok((vaddr@, frame@)),
                    Err(()) => Err(()),
                },
            ),
    ;
}
```

### Page Table Model & Implementation Proof

Concrete page tables must implement `PageTableInterface`. Two helper models aid proof:
- **Page Table Map Model**: Flat map representation.
- **Page Table Tree Model**: Tree-structured representation.

![](docs/pt_model.svg)

*Work in progress.*

