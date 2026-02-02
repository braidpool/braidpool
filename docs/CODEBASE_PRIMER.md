# Braidpool Codebase Primer

This document provides essential context for understanding the Braidpool codebase. Read this before contributing or reviewing code.

## Core Concepts

### Beads (not Blocks)
A **bead** is Braidpool's equivalent of a Bitcoin block, but with key differences:
- Beads can have **multiple parents** (unlike Bitcoin's single parent)
- Beads form a **DAG** (Directed Acyclic Graph), not a linear chain
- Beads are ~1000x more frequent than Bitcoin blocks (lower difficulty target)
- Every bead is a valid Bitcoin block template that *could* have been a Bitcoin block

**Code location**: `node/src/bead/mod.rs`

### Cohorts
A **cohort** is a set of beads that cannot be totally ordered with respect to each other, and may have appeared on the network close in time to each other. The cohort is also a graph cut, think of it as a "horizontal slice" through the DAG where *everything* on the right of the slice is a descendant of *everything* on the left.

- Cohorts are used to establish ordering and consensus
- Beads in the same cohort have arrived at roughly the same time
- The DAG is divided into sequential cohorts for payout calculations and difficulty targeting

**Code location**: `node/src/braid/mod.rs`

### DAG (Directed Acyclic Graph)
Unlike Bitcoin's blockchain (a linked list), Braidpool uses a DAG where:
- Each bead references **multiple parents** (typically 2-5)
- This eliminates orphan/stale blocks—all valid beads are included
- The structure handles network latency gracefully

```
    ┌─────┐
    │  A  │
    └──┬──┘
       │
   ┌───┴───┐
   ▼       ▼
┌─────┐ ┌─────┐
│  B  │ │  C  │   ← B and C are in the same cohort
└──┬──┘ └──┬──┘
   │       │
   └───┬───┘
       ▼
    ┌─────┐
    │  D  │       ← D has both B and C as parents
    └─────┘
```

### Highest Work Path (HWP)
The **Highest Work Path** is the path through the DAG with the most cumulative proof-of-work. It's analogous to Bitcoin's "longest chain" but for a DAG.

- Beads on the HWP are highlighted in the dashboard

### UHPO (Unspent Hasher Payout Output)
Braidpool's equivalent of Bitcoin's UTXO, representing a miner's accumulated share of rewards. V1 of Braidpool will put this directly in the Coinbase. Better ways to do this are an active area of research.

- Tracks each miner's contribution (shares submitted)
- Settles to Bitcoin on-chain

## Directory Structure

```
braidpool/
├── node/                    # Rust node implementation
│   ├── src/
│   │   ├── bead/           # Bead data structure and validation
│   │   ├── braid/          # DAG consensus (cohorts, ordering)
│   │   ├── behaviour/      # libp2p network behavior
│   │   ├── peer_manager/   # P2P peer connections
│   │   ├── ipc/            # Bitcoin Core IPC communication
│   │   ├── db/             # Database (persistence)
│   │   ├── stratum.rs      # Stratum mining protocol
│   │   ├── rpc_server.rs   # JSON-RPC API
│   │   └── main.rs         # Entry point
│   └── Cargo.toml
├── dashboard/              # React/TypeScript visualization
│   ├── src/
│   │   ├── components/
│   │   │   ├── BraidPoolDAG/  # D3.js DAG visualization
│   │   │   ├── BeadsTab/      # Bead explorer
│   │   │   └── ...
│   │   └── types/          # TypeScript interfaces
│   └── package.json
├── tests/                  # Integration tests and simulator
│   └── simulator.py        # Python DAG simulator
└── docs/                   # Specifications and documentation
    ├── braidpool_spec.md   # Full specification
    ├── braid_consensus.md  # Consensus algorithm
    └── overview.md         # High-level overview
```

## Key Files to Understand

| File | Purpose |
|------|---------|
| `node/src/bead/mod.rs` | Bead structure, serialization, validation |
| `node/src/braid/mod.rs` | Cohort calculation, DAG ordering |
| `node/src/behaviour/mod.rs` | P2P gossip protocol (libp2p) |
| `node/src/stratum.rs` | Stratum protocol for miners |
| `node/src/ipc/client.rs` | Bitcoin Core communication |
| `dashboard/src/components/BraidPoolDAG/` | DAG visualization |
| `docs/braidpool_spec.md` | Authoritative specification |

## Data Flow

```
1. Node creates Bead template:
   - Fetches block template from Bitcoin Core (via IPC)
   - Selects parent beads (current DAG tips)
   - Builds coinbase with commitments
   - Calculates merkle root
           │
           ▼
2. Template sent to miner via Stratum
           │
           ▼
3. Miner searches for valid nonce
   - Iterates nonce/extranonce
   - When hash meets Braidpool difficulty → share found
           │
           ▼
4. Miner submits share via Stratum
   - Node completes the Bead with winning nonce
   - Validates the Bead
           │
           ▼
5. Bead broadcast via P2P gossip (libp2p)
           │
           ▼
6. Receiving nodes:
   - Validate bead (hash, parents, signature)
   - Add to DAG
   - Recalculate cohorts
   - Update HWP if needed
           │
           ▼
7. Dashboard displays via WebSocket
```

## Common Patterns

### WebSocket Data (Dashboard)
The dashboard receives real-time updates via WebSocket:
```typescript
{
  parents: { [beadHash: string]: string[] },  // bead → parent hashes
  cohorts: string[][],                         // array of cohort arrays
  highest_work_path: string[],                 // HWP bead hashes
}
```

### Error Handling (Rust)
Use `?` operator and custom error types—no `unwrap()` in production:
```rust
// Good
let bead = Bead::from_bytes(&data)?;

// Bad
let bead = Bead::from_bytes(&data).unwrap();
```

### Async Patterns (Rust)
The node uses Tokio for async. Common patterns:
```rust
// Spawning tasks
tokio::spawn(async move { ... });

// Channels for cross-task communication
let (tx, rx) = tokio::sync::mpsc::channel(100);

// Avoid blocking in async context
// Use tokio::fs, not std::fs
```

## Glossary

| Term | Definition |
|------|------------|
| **Bead** | A share in Braidpool's DAG (like a block but with multiple parents) |
| **Cohort** | A set of beads at the same "height" in the DAG |
| **DAG** | Directed Acyclic Graph—the data structure holding all beads |
| **HWP** | Highest Work Path—the heaviest chain through the DAG |
| **UHPO** | Unspent Hasher Payout Output—miner's accumulated rewards |
| **Difficulty Epoch** | Bitcoin's ~2 week difficulty adjustment period |
| **Full Proportional** | Payout algorithm: rewards ∝ shares submitted |
| **Share** | A bead; proof of work submitted by a miner |
| **Tip** | A bead with no children (latest beads in the DAG) |

## Specification References

For detailed protocol rules, see:
- [`docs/braidpool_spec.md`](braidpool_spec.md) - Full specification
- [`docs/braid_consensus.md`](braid_consensus.md) - Consensus algorithm
- [`docs/overview.md`](overview.md) - High-level overview

## See Also

- [CONTRIBUTING.md](../CONTRIBUTING.md) - How to contribute
- [README.md](../README.md) - Running the node
- [CODE_REVIEW_CHECKLIST.md](CODE_REVIEW_CHECKLIST.md) - Review guidelines
