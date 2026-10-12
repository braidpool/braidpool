# EDCA Bead Validation

**Scope**: how a single bead is validated, and the committed-mempool cache that
validation reads. Two entry points only — **self-mined** and **received from a
peer**. IBD is out of scope. Payout roster construction is out of scope: by
construction it re-validates nothing.

**Tags**: **[live]** exists in code · **[gap]** does not exist · **[wrong]**
exists but diverges from `docs/EDCA/PAPER.md` or `docs/braidpool_spec.md`.

---

## 1. The invariant

> Both entry points must produce **byte-identical** stored values for the same
> bead.

If the self-mining path stores a different `S_i` than a peer would derive, this
node computes a different `U_m` than its peers — a payout fork, caused by a
perfectly valid bead. Every design choice below follows from this.

### Current asymmetry

| | self-mined | peer |
|---|---|---|
| PoW checked | **[live]** `is_met_by` — `stratum.rs:912`, `:1514` | **[gap]** nothing |
| coinbase reconstructed | **[live]** `coinb1 ‖ en1 ‖ en2 ‖ coinb2`, `stratum.rs:1101-1106` — node-owned prefix/suffix, already the right shape | **[gap]** nothing |
| merkle root from own branch | **[live]** `calculate_merkle_root`, `stratum.rs:1127` | **[gap]** nothing |
| `F_i` derived | **[wrong]** taken from `blocktemplate.fee_total_sats` | **[gap]** nothing |

`Braid::extend` (`braid/mod.rs:90-207`) checks parents, duplicates and orphans —
no proof of work, no merkle, no fees. So a gossiped bead is scored today having
passed no validation at all, while a self-mined one has passed two of the hardest
checks. That asymmetry *is* the invariant violation.

> **[wrong]** `lib.rs:364` hardcodes `weak_target = 1d00ffff` (difficulty 1) on the
> production path, while `stratum.rs:1245` already computes the miner's real
> assigned target one path over (that one is audit-mode). So every production bead
> claims difficulty-1 work, `block_probability_q` returns a near-zero probability,
> all beads score alike, and the truncation threshold prunes the entire state.
> Plumb `miner_target` through `propagate_valid_bead`.

---

## 2. The trust boundary

A bead on the wire is `block_header` + `committed_metadata` +
`uncommitted_metadata` (`bead/mod.rs:43`). It carries **no coinbase** — spec:63-64:
*"The coinbase transaction itself is not communicated because it can be
independently computed."*

| the verifier is **given** | the verifier **derives** |
|---|---|
| `block_header` (80 bytes, mined) | the committed-mempool state at the bead's position |
| `committed_metadata` — incl. the 2-5 delta transactions, in full | the canonical transaction order, hence the coinbase merkle branch |
| `uncommitted_metadata` — `en1`, `en2`, timestamps | the payout roster at that position |
| | the coinbase, and therefore its txid |
| | `F_i`, and therefore `A_i` and `S_i` |

**The rule**: a miner-supplied value may be accepted only when it reduces to
something the node independently holds. `parents` qualifies — each is a hash that
must resolve in `bead_index_mapping` (`braid/mod.rs:111`), so a parent cannot be
invented. `transaction_ids[0]` does not — it is 32 bytes compared against nothing.

> **[wrong]** `CommittedMetadata.transaction_ids: TxIdVec` holds the whole block's
> txid list (~96 kB). spec:103-104 specifies `transactions | List of serialized
> transactions` plus `transaction_cnt` — the 2-5 **full delta transactions**
> (~1-2 kB). Full bytes are required: the receiver must price them and hand them
> to its own cmempool instance.

---

## 3. The committed-mempool cache

### 3.1 What validation needs from it

For a bead `X`, validation needs four things about the state `X` was mined on:

| need | used by |
|---|---|
| `base_fees` — Σ fees over the state | step 8, to derive `F_i` |
| **membership** — is a txid already in the state? | step 6, delta disjointness |
| the **coinbase merkle branch** for the state in canonical order | step 7, the fold |
| the **payout roster** at that point | step 7, to reconstruct the coinbase |

All four are deterministic functions of the DAG. None may come from the bead.

### 3.2 Why one entry per cohort, not per bead

spec:161-163: *"we begin at the head of a cohort (all beads at the head of a
cohort have the same parents and ancestors by definition, and therefore the same
committed mempool)."*

So the state is shared by every bead at a cohort head. One entry per cohort.

### 3.3 Structure and sizing

A naive per-cohort member set is ~96 kB (≈3,000 txids × 32 B) × ~930 retained
cohorts ≈ **93 MB**. Unacceptable. Two observations collapse it:

- within an epoch the state only **grows** — transactions never leave until the
  epoch ends (§3.6), so one live set suffices for all cohorts
- `base_fees` is a **prefix sum** over cohorts, so it is 8 bytes per cohort

```rust
/// Live membership for the current epoch. Maps a txid to the cohort sequence
/// that introduced it, so membership in the state at cohort `n` is a single
/// lookup and a comparison.
pub struct EpochMembers {
    introduced_at: HashMap<Txid, CohortSeq>,
    /// Σ fees of every transaction introduced in each cohort, cumulative.
    /// `cumulative_fees[n]` is `base_fees` for the state at cohort `n`.
    cumulative_fees_sats: Vec<u64>,
    anchor: BlockHash,
}

impl EpochMembers {
    /// Is `txid` in the committed mempool as of cohort `at`?
    pub fn contains_at(&self, txid: &Txid, at: CohortSeq) -> bool {
        self.introduced_at.get(txid).is_some_and(|seq| *seq <= at)
    }
    /// `base_fees` for the state at cohort `at`.
    pub fn base_fees_at(&self, at: CohortSeq) -> u64 { /* index */ }
}

/// Per-cohort values that genuinely differ cohort to cohort.
pub struct CohortState {
    /// Canonical identity of the state: H(sorted txids). Identical on every
    /// node for the same state. Used as a checksum, not a lookup key — see §3.5.
    pub state_key: StateKey,
    /// Merkle siblings above the coinbase for this state, canonical order.
    pub coinbase_branch: Vec<[u8; 32]>,
    /// Payout roster at this point, for coinbase reconstruction.
    pub roster: Vec<TxOut>,
}
```

| component | size | × retained | total |
|---|---|---|---|
| `introduced_at` | ~40 B/tx × ~3,000 | once per epoch | ~120 kB |
| `cumulative_fees_sats` | 8 B | ~930 | ~7 kB |
| `coinbase_branch` | ~12 × 32 B = 384 B | ~930 | ~357 kB |
| `roster` | ≤64 × ~40 B = 2.5 kB | ~930 | ~2.3 MB |
| | | | **≈ 2.8 MB / epoch** |

Store a roster digest instead of the roster and it drops to ~0.5 MB, at the cost
of recomputing the roster on each reconstruction.

### 3.4 Construction — incremental, on cohort close

Never by ancestor traversal. When cohort `n` closes:

```
for each bead in cohort n, in canonical bead order:
    for each tx in that bead's delta:
        if introduced_at.insert(txid, n).is_none():   # genuinely new
            fees_this_cohort += fee(txid)
cumulative_fees_sats.push(cumulative_fees_sats.last() + fees_this_cohort)
coinbase_branch = branch over the ordered state
state_key       = H(sorted txids of the state)
roster          = EDCA roster at this cohort head
```

Cost is O(cohort size × 5), not O(|state|).

**Canonical bead order** (spec:161-177): transactions from beads on the
highest-descendant-work path first, then off-path beads in order of work. Work is
SSDW (spec:340-350); ties break on higher ancestor work, then lowest hash.
**[live]** `bead_cmp` at `braid/mod.rs:1014`, `descendant_work` at `:940`.

**Conflicts** (spec:172-177): children must not carry transactions conflicting
with their parents, per `MempoolAccept`. Off-path beads may conflict; add those in
bead-work order **ignoring failures**. `MempoolAccept` decides and work order makes
the sequence identical on every node — that is the deterministic tiebreak.

> **[gap]** `get_all_ancestors` / `updating_ancestors` must **not** be used here.
> `braid/mod.rs:648` clones the entire ancestors map inside its per-parent loop —
> it cannot be on an ingest path at any scale.

### 3.5 Lookup, and what the state key is actually for

Lookup is by **cohort sequence**, reached from the bead's parents — O(1), no
hashing, no search.

The state key is **not** the lookup key. It cannot be: you would have to derive
the state before you could look up the state. Its job is verification —

```
derived state  →  H(sorted txids)  →  compare to stored state_key
```

That is an O(1) check that your incremental chain still agrees with the content it
claims to represent. It catches a bug in the delta accumulation, and it catches
divergence against a peer: two nodes that disagree about a state disagree about
its key, visibly, instead of silently computing different payouts.

So the combined-hash-of-every-transaction earns its place as a **checksum**, off
the critical path.

### 3.6 Epoch scoping and invalidation

**Epoch.** The state is anchored to `prev_blockhash` and resets at each new
Bitcoin block. Within an epoch no delta transaction can have confirmed —
confirmation is what ends the epoch — so every transaction in a live state is
unconfirmed and priceable. Beads on different `prev_blockhash` have incomparable
states.

**Cohort nuke.** `extend` removes every cohort after the earliest one containing
the new bead's parents (`braid/mod.rs:142-160`). Roll back to cohort `k`:

```
truncate cumulative_fees_sats, coinbase_branch, roster, state_key at k
remove introduced_at entries with seq > k
```

Cost is O(deltas since `k`). Nuke depth is set by how far back a bead's parents
reach — **which is miner-chosen**, so one cheap bead can force deep
recomputation. **Bound parent depth** (within the epoch, or N cohorts of the tip).
This is the one attack in §7 with no natural guard.

---

## 4. The keystone: one fold covers every committed field

spec:87-92 requires the metadata hash to sit in an `OP_RETURN` in the coinbase,
with the transaction tree computed deterministically by each node, and *"in order
to be a valid share the resultant Merkle root must match the Merkle root in the
block header."*

With that wired, validation's central check is:

```
metadata_hash = H(bead.committed_metadata)
coinbase      = node_prefix(height, metadata_hash, roster) ‖ en1 ‖ en2 ‖ node_suffix
accept iff fold(txid(coinbase), coinbase_branch) == bead.block_header.merkle_root
```

Because the metadata hash is inside the coinbase, **altering any committed field
changes the coinbase txid and breaks the fold.** One check simultaneously confirms
`fee_total_sats`, `weak_target`, `payout_address`, `parents` and the delta are
exactly what the miner mined — and that the transaction set is the one *this node*
derived, because the branch came from the cache, not the bead.

> **[live]** The fold is already consistent between producer and verifier:
> `root_from_branch`/`hash_pair` (`validate_fees.rs:377-391`) computes
> `sha256d(current ‖ sibling)` with the coinbase always the left child —
> byte-identical to `template_creator::calculate_merkle_root` (`:168-180`), which
> built the header at `stratum.rs:1127`. Duplicate implementations, no cross-test;
> the binding rests on them agreeing.
>
> **[live]** The OP_RETURN machinery exists: `build_braidpool_op_return`
> (`template_creator.rs:288`), `MAX_BRAIDPOOL_COMMITMENT_LEN = 72`.
> **[gap]** It takes the commitment as a parameter and `committed_metadata` never
> reaches `template_creator`. Until wired, nothing in `committed_metadata` is bound
> to the work.

### Pre-committed is not correct

The fold proves the miner **pre-committed** to `fee_total_sats = 11,300` before
hashing. It does not prove 11,300 is right. Three checks, three distinct claims:

| check | proves |
|---|---|
| PoW | the work behind the commitment is real |
| fold | the miner committed to these exact values, on the set the node derived |
| derive `F_i` | the committed fee value is actually correct |

**Reconstruction is what makes the fold non-vacuous.** Accept the miner's coinbase
instead and both inputs become miner-chosen — `transaction_ids[0]` is arbitrary,
`merkle_root` is arbitrary, and the branch is public — so the miner sets
`merkle_root := fold(anything, branch)` and passes for free, with no transactions.

**Pin the extranonce window width**, or a miner shifts bytes between the
node-built prefix and the extranonce region and alters the node-derived part.
Stratum negotiates this per connection, which a remote verifier cannot see.

---

## 5. The pipeline

Cheapest first, so nothing expensive runs for a bead that cost nothing to make.

| # | check | cost | self-mined | peer |
|---|---|---|---|---|
| 1 | decode bounds | free | n/a — built locally | **required** |
| 2 | structural: `\|δ\| ≤ 5`, no duplicate txids, **parents antichain** | O(\|parents\|) | verify anyway | **required** |
| 3 | **PoW** `H(b) ≤ T_bp` | 1 hash | present, but against the miner's assigned target — must also check `T_bp` | **required** |
| 4 | parents resolve in `bead_index_mapping` | O(\|parents\|) | trivial (local tips) | **[live]** |
| 5 | cohort state from the cache (§3.5) | O(1) | from `local` | derive |
| 6 | delta disjointness — `contains_at` per txid | O(5) | checked at selection | **required** |
| 7 | reconstruct coinbase, fold, compare (§4) | ~12 hashes | **[live]** | **required** |
| 8 | derive `F_i`, compare to committed | O(5) | currently taken from the template | **required** |

**Steps 1-3 must run before parking an orphan.** Orphans are parked at
`braid/mod.rs:117` before any checks, and the pool is uncapped, un-deduped and
rescanned on every `extend` — so without a PoW gate it is a free memory sink for
beads whose parents never arrive. Promotion re-enters `extend`
(`braid/mod.rs:230`), so state-dependent checks (5-8) are correctly deferred to
then.

> **[wrong]** The dedup at `braid/mod.rs:122-127` is
> `self.beads.iter().any(|b| compute_bead_hash(b) == h)` — an O(N) double-SHA256
> scan under the write lock, while `bead_index_mapping` (`:38`) is used one line
> earlier. ~0.5 s CPU per bead at N=1e6.

### Step 1 detail

> **[wrong]** `TimeVec::consensus_decode` calls `Time::from_consensus(t).unwrap()`
> (`committed_metadata/mod.rs:34`), which errors below 500,000,000 — so a
> `parent_bead_timestamps` entry of `0` **panics the gossip decoder**, remotely,
> pre-PoW, from ~40 bytes. Violates CLAUDE.md's no-`unwrap()` rule.
>
> **[wrong]** `Vec::with_capacity(len as usize)` on an attacker-declared `u64`
> before reading any element — `TimeVec` (`:31`), `TxIdVec` (`:55`). A declared
> `u64::MAX` aborts the process.

### Step 2 detail

The antichain rule — PAPER Definition 2, spec:286-291 — requires
`∀ pᵢ, pⱼ ∈ P(b), pᵢ ∉ Ancestors(pⱼ)`.

> **[gap]** Not enforced at ingest. `check_cohort_ancestors` exists at
> `braid/mod.rs:1183` but is only reachable from `check_cohort` (`:1157`).

It is load-bearing for §3: PAPER Definition 2 exists to keep the DAG a minimal
transitive reduction and bound "the algorithmic complexity required to traverse
the DAG and compute the valid graph cuts". Without it a bead names redundant
transitive parents and inflates traversal cost for free.

### Step 3 detail

PAPER Definition 1: a bead is valid iff `H(b) ≤ T_bp`, the **global pool target**.
It is also the braid's *only* admission rule — spec:303-305: *"we keep all beads
with a valid PoW, regardless of whether they are considered invalid in other
ways"*, because work-weighted conflict resolution needs both sides of a conflict.

Until this exists, beads are free to produce and every cost figure in this
document is wrong by an unbounded factor.

### Step 8 detail

```
F_i = base_fees_at(cohort_seq)  +  Σ fee(t) for t in δ
       ↑ O(1) from the cache        ↑ ≤5 lookups
```

Never a sum over the state. Compare against the committed value; the derived value
is authoritative either way.

Delta transactions are priced by handing them to the node's own cmempool instance
— spec:152-155: *"an instance of the Mempool object in bitcoind using IPC ...
leverage all of the mempool validation and transaction selection logic in
bitcoind."* Epoch scoping (§3.6) guarantees they are unconfirmed, hence acceptable
to `MempoolAccept`.

> **[gap]** `mining.capnp` has `removeTxFromMempool` (`:22`) but **no add-tx
> primitive**, and `createNewBlock` takes only `useMempool :Bool` (`:40`) — no
> transaction list. The add side of spec:152-155 is unimplemented.
>
> If a delta cannot be priced: **defer**, never score at zero. A node scoring an
> unpriceable bead at zero while a peer prices it correctly *is* a payout fork —
> which deletes `FeeVerdict::Unknown => 0` (`score.rs:66`) as a safe default.

---

## 6. The shared entry point

```rust
/// The single gate every bead passes before it may extend the braid.
///
/// Both the self-mining path and the peer-gossip path call this, so the score
/// persisted for a bead is independent of how it arrived. `local` is a *cache*,
/// never a branch: on the self-mining path the node already knows the cohort
/// state, the delta prices and the coinbase, so passing them avoids
/// recomputation — but validation computes the same result either way, and a
/// disagreement between `local` and the derivation is a bug, not a preference.
pub fn validate_and_score(
    bead: &Bead,
    braid: &Braid,
    members: &EpochMembers,
    cohort: &CohortState,
    config: &EdcaConfig,
    local: Option<&LocalTemplate>,
) -> Result<BeadScore, BeadVerdict>;

/// Persisted on success. **Undecayed** — decay is a function of age, and cohort
/// reassignment changes ages but never raw scores, so a stored decayed weight
/// goes stale while a stored raw score never does.
pub struct BeadScore {
    pub raw_score_q: u128,
    pub fee_total_sats: u64,
    pub cohort_seq: CohortSeq,
}

pub enum BeadVerdict {
    /// Permanently invalid. Never store, never extend.
    Reject(BeadRejection),
    /// Undecidable *for now* — missing parent, unpriceable delta, unknown
    /// `prev_blockhash`. Park and retry. Never score at zero.
    Defer(BeadDeferral),
}
```

Debug-assert `local` against the derivation. A disagreement means the self path
has drifted from the peer path, which is a fork against your own peers.

> **[wrong]** `EdcaState::from_braid` rescores the whole retained window on every
> call and invokes `amplifier.fee_sats(bead)` per bead. None of the three
> `AmplifierSource` impls fits: `CommittedFeeAmplifier` trusts the miner's claim,
> `VerdictAmplifier` re-verifies every call. A fourth is needed that **reads the
> persisted `BeadScore`**.

---

## 7. Worked case

`r = 99/100`, `L_dust = 546`, `B_base = 312,500,000`, `D_bp/D_network = 1e-4`.

```
     G
    / \
   A   B     cohort 1    A, B concurrent — both parent G
    \ /
     C       cohort 2    C names both A and B
```

Cache after cohort 1 closes:

| field | value |
|---|---|
| `introduced_at` | t1..t3 → 0 · t4, t5 → 1 (from δA) · t6 → 1 (from δB) |
| `cumulative_fees_sats[1]` | 6,000 + 2,000 + 800 = **8,800** |
| `state_key[1]` | `H(sorted{t1..t6})` |
| `coinbase_branch[1]` | branch over {t1..t6} in canonical order |
| `roster[1]` | EDCA roster at cohort-1 head |

Bead `C` arrives: parents `{A, B}`, `δC = {t7(2500)}`, committed
`fee_total_sats = 11,300`.

| step | result |
|---|---|
| 1 | decodes within bounds ✓ |
| 2 | `\|δC\|=1 ≤ 5` ✓ · no duplicate txids ✓ · `A ∉ Anc(B)`, `B ∉ Anc(A)` ✓ |
| 3 | `H(C) ≤ T_bp` ✓ |
| 4 | `A`, `B` resolve in `bead_index_mapping` ✓ |
| 5 | parents are cohort-1 tips → `cohort_seq = 1` → cache entry, O(1) |
| 6 | `contains_at(t7, 1)` = false ✓ |
| 7 | `H(metadata)` → coinbase → `fold(txid, coinbase_branch[1])` == `C.header.merkle_root` ✓ |
| 8 | `F_C = 8,800 + 2,500 = 11,300` ✓ matches the commitment |

Persist:

```
A_C = 312,500,000 + 11,300 = 312,511,300
S_C = 1e-4 × 312,511,300   = 31,251.13     ← stored undecayed, never recomputed
```

---

## 8. Attack cases through the same pipeline

| case | caught at | response |
|---|---|---|
| claims `fee_total_sats = 50,000` | 8 — derived 11,300 ≠ 50,000 | reject |
| sets `merkle_root` arbitrarily | 7 — reconstructed coinbase + cached branch do not fold to it | reject |
| alters any committed field in flight | 7 — metadata hash changes the coinbase txid | reject |
| names parents `{A, G}`, `G ∈ Anc(A)` | 2 — antichain, O(\|parents\|) | reject |
| repeats a txid in `δ` | 2 | reject — also avoids the `UNIQUE(bead_id,txid)` insert failure in `db_handlers.rs` |
| claims `weak_target ≤ bits` for probability `ONE` (`score.rs:97-99`) | 3, **only if** `weak_target` is checked against the real PoW and `x_0` — see V1 | reject |
| no valid PoW | 3 | reject; nothing after step 3 runs |
| unknown parent | 4 | **defer** — orphan, retry |
| delta not priceable here | 8 | **defer**; zero-by-rule after N cohorts (V4) |
| **very old parents, to force a deep cohort nuke** | **uncaught** | bound parent depth (§3.6, V5) |

---

## 9. Prerequisites

| id | item |
|---|---|
| **V1** | **Uniform `D_bp` or miner-selected difficulty?** PAPER §3.2 requires a uniform global target, in which case `weak_target` never enters scoring and `block_probability_q` should use a protocol constant. spec:419-442 allows miner-selected `x_b ≤ x ≤ x_0`, in which case the current per-bead formula is right but `weak_target` **must** be validated at step 3 against both the real PoW and `x_0`. The implementation has silently chosen miner-selected without the validation that choice requires. |
| **V2** | Add-tx-to-cmempool IPC primitive — spec:152-155 intends it, `mining.capnp` lacks it. Blocks step 8 for peer beads. |
| **V6** | Extranonce window width: protocol-fixed, or carried in the bead. Blocks step 7 for peer beads. |
| **V4** | Staleness bound for an unpriceable delta — how many cohorts before zero-by-rule. |
| **V5** | Parent-depth bound, to cap cohort-nuke and cache-invalidation cost. |
| **V7** | `r` default — the shipped 80/100 is PAPER §4's explicitly "quite aggressive" illustration; §4.2 recommends > 0.9. |
| — | Wire `committed_metadata` into the coinbase `OP_RETURN` (§4). Without it step 7 binds nothing. |
| — | Plumb `miner_target` through `propagate_valid_bead`, replacing the hardcoded `1d00ffff` (§1). |
