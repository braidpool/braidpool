# EDCA Bead Validation — Design Baseline and Findings

**Status**: design in progress. Not implemented. No code on
`edca_payout_implementation` performs any of the validation described here.

**Scope**: re-verification of the committed fee total `fee_total_sats`, which
feeds the EDCA amplifier `A_i = B_base + F_i`. **Fee validation only.** Payout
roster correctness (O1) and EDCA parameter sanity (O8) are recorded below for
continuity but are explicitly out of scope; `weak_target` (O6) and the
`committed_metadata` signature gap (O7) matter here only where they share an
ingest-time mechanism with the fee check.

### 0. The central hypothesis to test

Narrowing to fees alone appears to simplify the design sharply. `F_i` needs only
the **transaction set**, and the set is proven by the fold:

```
fold(claimed_coinbase_txid, derived_branch) == bead.block_header.merkle_root
```

If that holds, the non-coinbase leaves are exactly `S(X)` in canonical order, so
the tx set is proven **regardless of what the coinbase contains**. The
coinbase's outputs, its BIP34 height and its payout roster are all irrelevant to
`F_i`.

If true, this means: no coinbase reconstruction is needed for fee validation
(§2.8 is a roster concern, not a fee concern), no cache of node-local coinbase
material is needed (§2.5–2.6), and O1's global-key/local-value problem does not
arise in the fee path at all. Fee validation becomes universal and cacheless.

**This hypothesis is what the two agents are tasked to test** — the iterator by
building on it, the auditor by trying to break it with a cross-field attack. It
is not yet established.

---

## 1. The problem

A `Bead` on the wire (`node/src/bead/mod.rs:43`) is:

```rust
pub struct Bead {
    pub block_header: BlockHeader,                 // 80 bytes, PoW-bound
    pub committed_metadata: CommittedMetadata,     // txids, parents, payout_address,
                                                   // min/weak_target, fee_total_sats
    pub uncommitted_metadata: UnCommittedMetadata, // extranonce1, extranonce2,
                                                   // broadcast_timestamp, signature
}
```

It carries **no transactions and no coinbase**.

The bead hash is `network.block_hash(block_header)` (`node/src/utils/mod.rs:41`) —
the header alone. `committed_metadata` is not in the hash preimage and is never
embedded in the coinbase (`template_creator.rs` never references it). So the
field group named "committed" is bound to the proof of work by exactly **one**
mechanism: the merkle root, covering `transaction_ids` only.

`fee_total_sats`, `weak_target`, `min_target` and `payout_address` have no
cryptographic binding to the work. The `comm_pub_key`/`signature` pair that
could authenticate them is never verified anywhere in the tree (and is a
hardcoded constant at `lib.rs:385`).

### 1.1 Why the existing module does not close this

`node/src/edca/validate_fees.rs` offers three routes. Strength runs **opposite**
to data requirements:

| route | function | verdict | why |
|---|---|---|---|
| 1 | `verify_fee_commitment` (46–126) | **unsound alone** | derives the fee from miner-supplied coinbase value *and* miner-supplied BIP34 height; neither is consensus-capped for a weak share. Checks miner data against miner data. Also needs a `&Transaction` a bead does not carry. |
| 2 | `verify_fee_bound` (320–354) | **right check, wrong data** | `claim ≤ known fees` is the correct direction, but needs every tx and its prevouts. `saturating_add` at 331 can report `Proven` on saturation. Nothing consumes `FeeBound`. |
| 3 | template route (415–619) | **sound, local-only** | fee comes from the node's own `fees_sats`; the bead is tied to it by folding the coinbase txid up the node's own branch to the work-bound header root. Only covers templates *this* node issued → `Unknown` → `F_i = 0` for every bead from another node. |

Route 1's merkle check upgrades the coinbase from *unauthenticated* to
*pre-committed*, not to *correct*. A miner who commits to a lie before hashing
is still lying; the PoW only proves they did not change their mind afterwards.

Every entry point in the file has **zero callers**. The only thing reachable
from outside is the `FeeVerdict`/`FeeVerdictSource` pair that `score.rs`
consumes, and nothing constructs a `TemplateCache` to serve it.

### 1.2 The rule this yields

> A verifier may accept miner-supplied data **only** when it reduces to a value
> the node independently holds.

Route 3 obeys it (miner's coinbase txid, checked against the node's branch and
the work-bound root). Route 1 does not.

### 1.3 The consequence larger than fees

In braidpool the coinbase is not the miner's to choose — it carries the pool's
payout roster (`template_creator.rs:389`; `braidpool_spec.md:70-73`). A bead
with a substituted coinbase is not primarily inflating a fee claim, it is
**rewriting the payout roster**.

Route 1 accepts such a bead. Route 3 detects it but only degrades it to
`Unknown → F_i = 0` (`score.rs:66`) — the bead stays in the DAG and still
scores on `B_base`. **The `FeeVerdict` enum's worst outcome is "no fee credit";
there is no "invalid bead".** Proportionate to fee inflation, disproportionate
to coinbase substitution, where the harm is not in the fee claim.

Note the merkle path covers only the non-coinbase leaves, so a path match does
**not** constrain the coinbase: any coinbase txid folds up the path to *some*
root, and the header commits to that root. Fee validation and roster validation
are independent problems.

---

## 2. The design

### 2.1 Split the committed transaction list

```
committed_metadata.transaction_ids
  ├── cmempool_tx_ids    — from the deterministic committed-mempool state
  └── additional_tx_ids  — 2..5 miner-chosen txs from the miner's own bitcoind
```

`additional_tx_ids` enter the cmempool only if the bead is valid, so valid beads
advance the shared state and miners have a reason to relay new transactions.

### 2.2 The cmempool state is derived from the DAG, not stored

```
S(X) = ⋃ S(parents of X)  ∪  delta(X)       where delta(X) = additional_tx_ids
```

Consequences:

- The state a bead was mined on is a function of its **ancestor set**, which the
  verifier already walks to insert the bead (`Braid::resolve_parents`,
  `get_all_ancestors`). No snapshot store and no search is needed to obtain it.
- Two nodes cannot disagree about a state without disagreeing about the DAG.
  The cmempool stops being its own consensus object and becomes a projection of
  braid consensus.
- Rebuildable after restart; memoize `S(X)` per bead, computed incrementally
  from parents.
- State is **monotonically increasing along any path in the DAG**.

### 2.3 Validity rule for the delta

```
delta(X) ∩ S(ancestors of X) = ∅
```

A bead may only add transactions not already in the cmempool at its own
position. This is the "the additional txs exactly fill the delta" condition,
expressed as a validity rule rather than a lookup mechanism.

### 2.4 Epoch scoping

Monotone union holds only within one Bitcoin block. Scope state to
`prev_blockhash` and reset at each new Bitcoin block; beads on different
prev-hashes have incomparable states. This bounds snapshot retention to roughly
one block interval instead of the EDCA scoring window.

### 2.5 What is derivable and what is not

**Derivable from ancestors**: the tx set `S(X)`, its canonical order, and
therefore the whole merkle tree including the coinbase branch. The path never
needs caching — recompute the tree from the ordered set.

**Not derivable**: the coinbase the *issuing node* built. Its outputs depend on
that node's `EdcaConfig` (retention, dust limit, base subsidy), its
`max_outputs`, which addresses it could resolve, which miners it dropped as
over-budget — plus its pool tag, height view and extranonce sizing. None of
that is a function of the DAG.

### 2.6 Lookup key

```
key = hash(txid-sorted members of S(X))
```

Derivable by any node, identical everywhere, order-independent, and immune to
grinding (forcing a different snapshot needs a collision).

**Rejected alternative**: keying by the delta. The node hands out a job *before*
the miner picks their additional txs, so the delta is unknown at insert time —
the transition is created by the very bead being verified, making the index
circular. It is also not uniquely resolvable under concurrency: two beads on the
same `S_prev` adding `{a,b}` and `{b,c}` means neither bead's own delta equals
the delta between two stored snapshots.

### 2.7 The two checks are separate

| | needs | coverage | failure consequence |
|---|---|---|---|
| **Fee verification** | the tx set only — `F_i = Σ fees over S(X)` | **universal**, no cache; a tx fee is objective (`inputs − outputs`) so any node holding tx + prevouts computes the same number | wrong score |
| **Coinbase/roster verification** | the issuing node's coinbase material, via the cache | **key is global, cached value is node-local** → see O1 | theft of the block reward |

Collapsing both into "the merkle root matched, so the snapshot is right" is
exactly what let coinbase substitution through. Keep them separate: the failure
modes are not comparable.

### 2.8 Coinbase reconstruction

Do not accept a coinbase; rebuild it.

```
expected_txid = txid(node_derived_prefix ‖ en1 ‖ en2 ‖ node_derived_suffix)
accept iff fold(expected_txid, derived_branch) == bead.block_header.merkle_root
```

`en1`/`en2` are already in `uncommitted_metadata`. They need no authentication:
alter them and the reconstructed txid changes, the fold fails, the bead
self-rejects. Arbitrary content *inside* the extranonce window is harmless —
scriptSig bytes do not affect value.

**The extranonce window length must be protocol-fixed or carried in the bead.**
Otherwise a miner shifts bytes between the prefix and the extranonce region and
alters the node-derived part. Stratum negotiates extranonce size per connection,
which is not available to a remote verifier.

The fold itself is already consistent between producer and verifier:
`validate_fees::root_from_branch`/`hash_pair` (377–391) computes
`sha256d(current ‖ sibling)` with the coinbase always the left child, identical
to `template_creator::calculate_merkle_root` (168–180), which is what built the
header at `stratum.rs:1127`. Correct because the coinbase is leaf 0, so its
subtree is the left child at every level. These are duplicate implementations;
one should call the other, or the invariant needs a test — route 3's entire
soundness rests on them agreeing.

### 2.9 Unknown state must defer, not reject

A bead mined on a legitimate state this node has not built yet (behind on the
DAG, or cannot obtain the additional txs) must be **parked in the orphan pool
and retried**, reusing the handling `Braid::extend` already has for missing
parents. Permanent rejection means different nodes reject different beads and
the DAG forks. Reject permanently only when the state *is* known and the root
genuinely disagrees.

### 2.10 Verify once at ingest; score from storage

Do not let `EdcaState::from_braid` re-verify. If the amplifier re-derives `F_i`
on every rebuild, snapshots must be retained for the whole scoring window
(thousands of cohorts at a realistic `r`). Instead: validate at ingest, write
the verified `F_i` to the bead record — `fee_total_sats` is already a persisted
column — and have the amplifier read the stored, already-validated value.

### 2.11 No local filtering of the canonical set

Earlier in the design discussion it was suggested that nodes filter the
canonical cmempool locally when building a real template, so scoring determinism
would not inherit bitcoind-view divergence. **That is incompatible with §2.2**:
if a node filters, its job's tx set ≠ `S(X)`, the derived merkle root will not
match, and honest beads get rejected.

The version that survives: **no local filtering**. Enforce `additional_tx_ids`
validity at bead ingest — each additional tx checked against the state's implied
UTXO view before the delta is accepted. The canonical set is then internally
consistent by construction, and invalidity can only arise Bitcoin-side
(confirmed or replaced), which §2.4's epoch reset handles.

Cost: ingest needs the additional txs and their prevouts, so the node must fetch
them, and a bead whose additional txs it cannot obtain defers (§2.9).

---

## 3. Open problems

| id | problem |
|---|---|
| **O1** | **Roster-check coverage.** The lookup key is global but the cached coinbase material is node-local: two nodes building a job on the identical tx set produce different coinbases, so a bead from another node's job finds the wrong entry or none. Options: (a) consensus-fix the roster inputs (`EdcaConfig`, output budget, address-resolution rules, tag format) so the roster becomes DAG-derivable and the cache dissolves; (b) have the bead carry a commitment to the roster (or coinb1/coinb2 outright) — self-contained, costs bead size; (c) accept roster verification as local-only while fee verification stays universal. |
| **O2** | **Eviction across Bitcoin epochs vs. divergent bitcoind views.** A cmempool tx can become invalid against a node's UTXO view (parent confirmed, replaced, evicted) and each node sees that at a different time. Dropping diverges on timing; keeping makes the template unmineable. §2.4 + §2.11 push the problem to the epoch boundary but do not specify the reconciliation. |
| **O3** | **Double-spend tiebreak.** Two beads in the same cohort adding conflicting txs (same prevout). Needs a deterministic rule (lowest txid? lower bead hash wins?). |
| **O4** | **Canonical ordering spec.** txid sort under topological constraint — must be pinned exactly, or merkle roots diverge and honest beads are rejected. |
| **O5** | **Cold rebuild / IBD cost.** If the coinbase embeds the payout roster, verifying one bead needs the EDCA score of all its ancestors. The recursion is well-founded (each bead depends only on ancestors, no cycle) and steady state is cheap with per-bead memoization, but IBD becomes a sequential score-then-verify walk. Needs sizing. |
| **O6** | **`weak_target` / `bits` / `payout_address` are unvalidated.** `weak_target` is never checked against the header hash — `is_met_by` appears only at `stratum.rs:912` and `:1514`, on the node's own downstream submissions, never on a peer's bead. `score.rs` divides by `weak_target`, so a bead committing `weak_target ≤ bits` scores probability `ONE` (a full `A_i`). Same ingest point as the fee check. |
| **O7** | **`committed_metadata` is not bound to the PoW** and its signature is never verified. Signing it with `comm_pub_key` would bind `fee_total_sats`, `weak_target` and `payout_address` to someone. |
| **O8** | **EDCA parameter sanity** (separate from validation, same branch). Default `r = 80/100` gives a ~5-cohort window, which only balances if weak shares are ~50x easier than network difficulty; realistic difficulty needs `r ≥ 0.999`, whose table needs 44k+ entries against `MAX_DECAY_TABLE_LEN = 8192`. The prune threshold `L_dust·(1−r)` = 109.2 sats is compared against cohort aggregates whose scale at realistic difficulty is ~1e-6 sats, so every cohort is pruned on creation and `nominal_outputs` returns `EmptyState`. |

---

## 4. Findings

### 4.1 Audit verdict on §0: **the hypothesis BREAKS**

Full audit: [`edca_fee_validation_audit.md`](edca_fee_validation_audit.md)
(986 lines — 15 ground facts, 15-field validation matrix, sections A–D, 10-item
defect appendix, every claim with file:line).

**Why it breaks.** The fold has *two* miner-controlled inputs, not one:

- `claimed_coinbase_txid` = `transaction_ids[0]` — 32 arbitrary bytes, never
  compared against any actual transaction's txid anywhere in the tree
- `header.merkle_root` — chosen by the miner when building the header

`derived_branch` is **public**: anyone who can derive `S(X)` can derive
`branch(S(X))`. So a miner derives `S` themselves, computes `B`, picks any
32-byte `c`, sets `merkle_root := fold(c, B)`, and the equation holds **by
construction — for any `S`, with no transactions, no coinbase, no bitcoind.**
Degenerate case: `transaction_ids = [c]`, `merkle_root = c`, because
`root_from_branch(c, [])` returns `c` unchanged (`validate_fees.rs:386-390`).

The fold is a **binding** (non-malleable attribution under collision
resistance), never a **proof of possession**. It also does not pin leaf count:
odd-count duplication means `[cb,t1,t2]` and `[cb,t1,t2,t2]` share both root
*and* branch.

§0 was also self-defeating: coinbase reconstruction (§2.8) is the only thing
that makes the fold's left input a value the node holds. §0 violated the
design's own rule §1.2 while citing it. Dropping reconstruction does not
dissolve O1 in the fee path — it hides it.

### 4.2 Adjudication — what the break does and does not kill

- §0's **justification** ("the tx set is proven") is dead. It must not be used.
- But `F_i` was always to be computed by the **verifier** over its own
  derivation of `S(X)`; the miner never supplies the fee number. So forging the
  fold does **not** let a miner inflate `F_i` arithmetically. What it buys is
  fee credit without having held the transactions — which defeats the
  amplifier's purpose (rewarding miners who carry fee-paying txs), but is a
  weaker harm than inflation.
- The **actual inflation vector** is parent/delta selection: `parents` and
  `additional_tx_ids` are both miner-chosen, so the miner steers which `S(X)`
  the verifier derives, and additional txs admit unbounded claimed fees. The
  attacker can also make a fee unpayable (RBF/double-spend) while the tx stays
  in the DAG-derived cmempool (O2).

**Restated problem.** Not "prove the set", but: *constrain parent and delta
selection so the verifier computes `F_i` over a set the verifier chose, rather
than one the miner steered.* This is a different and harder problem than §0
framed.

### 4.3 Nothing is even pre-committed today

`Braid::extend` (`braid/mod.rs:90-207`) performs **no proof-of-work check**, and
`is_met_by` (`stratum.rs:912`, `:1514`) never touches a peer's bead. The merkle
root is bound to the header, but producing a header is free. **Every
"work-bound" / "PoW-committed" claim in §1 and §2 of this document is
conditional on a PoW check at ingest that does not exist.** A PoW check at
ingest is a prerequisite of the whole design, not an assumption.

### 4.4 Seven conditions for any salvage (audit §A.6)

C1 reconstructed left leaf · C2 `F` from the verifier only · C3 unique `S(X)`
(needs O2/O3/O4) · C4 an `F` bound independent of set membership · C5 PoW +
`weak_target` + `bits` checked · C6 `transaction_ids.len() == 1 + |S(X)|` plus
dedup · C7 hardened decode.

### 4.5 Live defects found in current code (independent of the design)

Verified directly, not taken from the agent report:

| # | defect | status |
|---|---|---|
| D1 | `TimeVec::consensus_decode` calls `Time::from_consensus(t).unwrap()` (`committed_metadata/mod.rs:34`). `from_consensus` errors below 500,000,000, so any `parent_bead_timestamps` entry of 0 **panics the gossip decoder**. Remote, pre-PoW, ~40-250 byte message. Also a direct violation of CLAUDE.md's "no `unwrap()` in production code". | **verified** |
| D2 | `Vec::with_capacity(len as usize)` on an attacker-declared `u64` length, before reading any element — `TimeVec` (`:31`) and `TxIdVec` (`:55`). A declared `u64::MAX` aborts the process. | **verified** |
| D3 | `verify_fee_bound` (`validate_fees.rs:329-339`) does not deduplicate txids and uses `saturating_add`, so a repeated high-fee txid inflates `computed_fees` linearly and a long enough list saturates to `u64::MAX`, returning `Proven` for *any* claim. `verify_fee_commitment` *does* dedup (`:69-72`); route 2 reached via route 3 skips it. | **verified by reading** |
| D4 | `extend`'s dedup is `self.beads.iter().any(|b| compute_bead_hash(b) == h)` (`braid/mod.rs:122-127`) — O(N) double-SHA256 per insert under the write lock, while the O(1) `bead_index_mapping` (`:38`) is already used for parent lookup at `:111`. ~0.5 s CPU/bead at N=1e6; ~1e6:1 attacker advantage. | **verified** |
| D5 | Duplicate txid passes `extend`, then violates `UNIQUE(bead_id,txid)`, rolling back the whole insert (`db_handlers.rs:320-351`); with `foreign_keys(true)` the missing `Bead` row FK-fails every descendant's `Relatives` insert — one bead poisons persistence of its whole descendant subtree, silent until restart. | agent-reported, **not yet verified** |
| D6 | Orphan pool (`braid/mod.rs:117`) is uncapped, un-deduped, parked *before* any check, and fully rescanned per extend. | agent-reported, **not yet verified** |

Quantified scoring impact: `fee_total_sats = MAX_MONEY` → `A_i` ~6.3e6x honest,
~99.84% of pool payout against a 10k-bead window. `score.rs:97-99` returns
probability `ONE` whenever `weak_target <= bits`, a further ~1e6x.
**Multiplicative: ~6e8x with zero work.**

### 4.6 Checks that would reject honest beads

Flagged so they are specified as score-at-zero or defer, never reject:
`payout_address` validation (the producer passes the Stratum *worker_name*,
`lib.rs:354`); signature verification (producer uses a hardcoded constant,
`lib.rs:384-389`); any §2.8 reconstruction before O1 is closed. Also
`parent_bead_timestamps` is never persisted — reload substitutes the parents'
own `start_timestamp` — so a future signature over `committed_metadata` would
fail for every reloaded bead.

### 4.7 Iterator findings

Full iterations: [`edca_fee_validation_iterations.md`](edca_fee_validation_iterations.md)
(1638 lines — hypothesis test, iterations 1-8, converged spec, decisions D1-D7).

The iterator broke §0 **independently and before being redirected**, reaching
the same two-miner-controlled-inputs break and demonstrating it numerically.
Convergent discovery by two agents working separately is the strongest evidence
available here that §0 is dead.

**Its conclusion on the fold: delete it, do not build on it.** A check that
everyone passes for free is worse than no check, because it reads as protection.
§0's three *conclusions* (no coinbase reconstruction, no node-local cache, O1
absent from the fee path) survive by a different route: `F_i` needs no proof
because it is **derivable**.

#### Four additional breaks, verified here

| # | finding | status |
|---|---|---|
| B5 | **The biggest finding.** `node/schema/mining.capnp` exposes `getTxFees` (`:29`), `getCoinbaseTx` (`:31`), `getCoinbaseMerklePath` (`:34`), `removeTxFromMempool` (`:22`), `submitSolution` (`:35`) — all scoped to *this node's own current template*. There is **no `getrawtransaction`, no UTXO/coin lookup, no mempool query by txid**. A peer-sourced transaction therefore **cannot be priced at all today**. "Universal and cacheless" fee validation is unreachable without a new bitcoind interface. | **verified** |
| B4 | `Transactions` (`schema.sql`) is `(bead_id, txid)` with `UNIQUE(bead_id, txid)` and **no ordinal column**; the restore query (`db_handlers.rs:483-484`) has **no `ORDER BY`**. Committed tx order is not preserved across restart, breaking any order-dependent design. | **verified** |
| B3 | `stratum.rs:1276` ships `transaction_ids: TxIdVec(Vec::new())`, so the fold is not even *evaluable* for beads from that path. | **verified earlier** |
| B6 | `get_all_ancestors`/`updating_ancestors` (`braid/mod.rs:622-661`) clones the **entire** ancestors map — `let ancestor_ref = ancestors.to_owned();` at `:648` — inside the per-parent loop. Cannot be on the ingest path at any scale. §2.2 leaned on exactly this function. | **verified** |
| — | Odd-leaf-count duplication means the root is not injective over the leaf multiset (independently matches the auditor). | agreed by both |

#### Accepted correction to §4.2

My framing ("parents *and* delta are miner-chosen, so the miner steers
`S(X)`") was wrong on parents. The union is **monotone**, and honest behaviour
already references all current tips, which is the maximal ancestor set — so
parent choice can only **shrink** a miner's own `F_i`, never inflate it.
Referencing older non-tip beads adds nothing, since they are already ancestors
of the tips.

**The delta is the sole inflation vector.** The narrower real vectors are
cross-epoch replay (fixed by epoch checks) and introduction timing (fixed by a
cap). Priority 1 was decided as `F_i` **includes** the delta — excluding it
kills §2.1's relay incentive and under-prices every bead.

#### Determinism resolved (priority 3)

A fee is a pure function of `(tx, UTXO@prev_blockhash)`, both consensus
objects. So determinism requires **availability, not identical mempools**.
Resulting invariant: **every unavailability must produce a defer, never a
number.** This deletes `FeeBound::Undecided`'s partial sum and
`FeeVerdict::Unknown => 0` (`score.rs:66`) as named payout forks — a node that
scores an unpriceable bead at zero while a peer prices it correctly *is* the
fork.

#### Iteration 8 — the capped ancestor-closure credit

```
F_i = base_credit(epoch) + Σ_{Y ∈ anc(X) ∪ {X}} min(Σ δ(Y) fees, MAX_DELTA_CREDIT_SATS)
```

Fixed once at ingest. Because beads cost work, this bounds an attacker's
marginal gain by their **hashrate** rather than by their fee claims, taking the
auditor's 4.20x cohort advantage down to 1.001x at a cap of `B_base/1000`. It
also removes set-wide fee re-summation from the hot path and preserves §2.10.

The iterator accepts the auditor's §A.4 as something it had under-weighted: the
attacker's fee is **real**, so a correct oracle prices it correctly and no
oracle hardening helps — only the cap does.

#### Storage

One persistent ordered set of bead indices per bead serves the `F_i` sum,
`S(X)`, and pairwise non-ancestrality: ~500 B/bead, ~300 kB/epoch, against
96 kB/bead (~9.6 GB IBD) naive. Deleting the fold for a `state_key` commitment
shrinks a bead **96.2 kB -> ~330 B (~290x)** and bead-sync IBD **9.6 GB ->
33 MB**, and makes canonical order a *sort*, which fixes B4 for free.

#### Wire format (spec item a)

**Yes to `version: u16`** — for forward dispatch, not compatibility. Positional
consensus encoding makes backward compatibility impossible. The live
`#[serde(default)]` (`committed_metadata/mod.rs:81`) concerns old **DB rows**,
not peers. A flag-day break is acceptable *now* — zero callers of
`validate_fees.rs` and of `EdcaState::from_braid`, both independently verified
— and will not be acceptable later.

### 4.8 Additional live defect: unchecked signed fee cast

| # | defect | status |
|---|---|---|
| D7 | `getTxFees` returns **`List(Int64)`** (`mining.capnp:29`), but `ipc/client.rs:456-457` does `fee_value as u64` — an unchecked signed-to-unsigned cast — and `:456` uses a plain `+` (panics on overflow in debug, wraps in release). `lib.rs:227` then `saturating_add`s the already-wrapped values, so **a single negative entry pins `fee_total_sats` at `u64::MAX`** for every bead on every template. Bitcoin Core's `CreateNewBlock` conventionally sets `vTxFees[0] = -nFees` for the coinbase slot; no Core source is vendored here, so **this must be confirmed upstream**. If the convention holds, the committed fee total is broken today. | mechanism **verified**; Core convention **needs upstream confirmation** |

### 4.9 Did not converge — maintainer decisions

| id | decision |
|---|---|
| **D2** | **The biggest scope call.** Does braidpool add a bitcoind interface for pricing peer-sourced transactions (UTXO/coin lookup or `getrawtransaction`)? Without it, fee validation cannot be universal, and the fee amplifier can only ever credit locally-known transactions. |
| **D5a** | How `base_credit` carries capped credits across an epoch boundary, when the cap deliberately blurs per-transaction attribution. |
| **D7'** | Whether a *capped* `F_i` is still the quantity EDCA's `A_i` is defined to be. Safety and paper-fidelity may be incompatible; this is a protocol-definition question, not an implementation one. |
| **D3** | Double-spend tiebreak. Recommendation: lowest introducing-bead hash, because cohort ordinals are unstable under `braid/mod.rs:141-199`. |
| **D6** | `MAX_DELTA_CREDIT_SATS` must be a hardcoded per-network constant, **not** an `EdcaConfig` field — it is `F_i`'s only unavoidable node-local dependence, and a configurable value is a payout fork. |
