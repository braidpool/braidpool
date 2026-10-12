# EDCA Fee Validation — Iterator Findings

**Agent role**: iterator (build on §0). **Scope**: re-verification of `fee_total_sats` /
derivation of `F_i` for `A_i = B_base + F_i`. Roster correctness (O1) and EDCA parameter
tuning (O8) are out of scope and appear only where fee validation cannot be specified
without them.

**Branch**: `edca_payout_implementation`. All line numbers verified by reading the tree
unless marked *unverified*.

**Document order note**: Part 1 tests §0 and breaks it. Parts 2-3 build the replacement.
Part 4 re-aims Iteration 3 onward after the auditor's break and the coordinator's
correction, and supersedes Iteration 3's framing of the fee cap; Part 3's spec is amended by
Part 4's "Delta to the Converged Specification". Part 5 lists what a maintainer must decide.

**The five priority questions, answered up front:**

| # | question | answer | where |
|---|---|---|---|
| 1 | Does `F_i` count the delta? | **Yes.** Excluding it makes `F_i` a function of the parents alone, so relaying transactions earns nothing and §2.1's incentive vanishes; it also under-prices every bead against the template actually mined. Consequence: the delta is the inflation vector, and it must be **capped per bead**. | It. 8 |
| 2 | Where does a fee come from? | Own-template `getTxFees` (free, already fetched), a persisted per-epoch fee table, in-state prevout resolution, and a chain query for confirmed prevouts. **The last does not exist** — `mining.capnp` has no UTXO or raw-tx access, so a peer-sourced transaction cannot be priced today. | Break 5, It. 3, D2 |
| 3 | Is `fee(t)` deterministic? | **Yes, conditionally.** A fee is a pure function of the transaction and the UTXO set at `prev_blockhash`, both consensus objects, so it needs *availability*, not an identical mempool view. The invariant: **every unavailability must produce a defer, never a number.** `FeeBound::Undecided`'s partial sum and `FeeVerdict::Unknown => 0` (`score.rs:66`) are payout forks and are deleted. | It. 3, It. 4 |
| 4 | Canonical ordering and key | Pinned byte-exactly as `SHA256d(prev_blockhash ‖ SHA256d(u32_le(n) ‖ sorted txids))`, sorting on `Txid::to_byte_array()` — **not** display order. The merkle fold is deleted, so no leaf ordering and no duplicate-last rule enters. | Spec (a), (b) |
| 5 | Where the check runs | A two-phase async gate above `Braid::extend` (`braid/mod.rs:90`), never inside it (`extend` is sync and re-entrant via `process_orphan_beads`). Phase A pure ⇒ permanent rejects; Phase B I/O ⇒ defers only. Every permanent reject is a pure function of `(bead, DAG, chain@prev_blockhash)`, so no honest bead is ever permanently rejected. | It. 4, It. 6-7 |

---

# Part 1 — Hypothesis Test

## The hypothesis under test (§0)

> `F_i` needs only the transaction set, and the set is proven by
> `fold(claimed_coinbase_txid, derived_branch) == header.merkle_root`.
> If that holds, the non-coinbase leaves are exactly `S(X)` in canonical order, so the tx
> set is proven regardless of what the coinbase contains — making coinbase reconstruction,
> the node-local coinbase cache, and O1 all irrelevant to the fee path.

**Verdict: the three conclusions survive. The argument does not.** The fold is a
tautology, not a proof, and should be deleted from the fee path rather than built on. The
conclusions hold by a different and stronger route: `F_i` need not be *proven by the bead*
at all, because it is *derivable by the verifier*. What §0 hides is that the hard problem
is not "which transaction set" (that is a DAG function) but "what fee does each
transaction pay" — and the current tree has **no bitcoind interface capable of answering
that for a transaction it did not itself template** (see Break 5).

## Break 1 — the fold is satisfiable for free; it has zero information content

Every quantity in the equation is either public or attacker-chosen, and the attacker
chooses last.

* `derived_branch` is derived by the verifier from `S(X)`, and `S(X)` is a pure function
  of the bead's parents (in the DAG, public) and its delta (in the bead, public). So the
  branch is computable by *anyone* holding the bead and the DAG — the honest verifier, the
  honest miner, and the attacker alike.
* `header.merkle_root` is 32 bytes the miner writes into the header **before** hashing. The
  miner picks it freely.
* `claimed_coinbase_txid` is `bead.committed_metadata.transaction_ids.0[0]`. On the wire it
  is an arbitrary 32-byte value: `TxIdVec::consensus_decode`
  (`node/src/committed_metadata/mod.rs:50-59`) reads raw 32-byte txids with no constraint,
  nothing in the tree checks it hashes any real transaction, and the bead carries no
  coinbase to check it against (`node/src/bead/mod.rs:43-48` — header + committed +
  uncommitted, no `txdata`).

The attack is one line: pick any `x`, compute `r = fold(x, B_derived)`, set
`header.merkle_root = r`, mine. The check then passes with probability 1 at a cost of
`|B| = ceil(log2(n+1))` sha256d compressions — about 12 hashes, ~15 µs, for a 3000-tx
template.

Numerically, with the worked example of Part 3 (`S(C)` = 5 txs, branch depth 3):

```
derived branch B      = [1111…11, 3df5a631…a512, c95487b9…fe21]
honest coinbase 0xc0… : fold = 8b1d740d01b13c4a13ed7478e0b450b12c3a00f777f736a8fb9669202738404a
garbage  x = deadbeef…: fold = 05925ed60504606ae0d6b33cbf1e1322d2e24f4436b032b0e429ee16c1b82b39
```

The attacker writes the second value into `header.merkle_root` and the fold verifies. The
attacker holds no transactions, no coinbase, and no mempool.

The implication in §0 is also circular as stated. *Deriving the branch from `S(X)` is what
defines the leaves* as `[x] ++ canonical(S(X))`; the equality then only reports that the
miner's root is the root of the tree the verifier has already built. With the root chosen
last, that is free. "The tx set is proven" is not a conclusion the equation can support.

## Break 2 — the merkle root is not an injective commitment to the leaf multiset

Bitcoin's merkle tree duplicates the last node at odd levels (CVE-2012-2459), and
`bitcoin::merkle_tree::calculate_root` — used at `node/src/edca/validate_fees.rs:74-79` —
implements that rule. For some leaf counts, lists `L` and `L ++ [last(L)]` produce the same
root. So "the non-coinbase leaves are **exactly** `S(X)`" is false even against an honest
miner: the root is consistent with a family of leaf lists. For fee purposes the ambiguity
is benign (it only ever duplicates a leaf already counted) but the hypothesis as written is
not sound, and any future use of the fold as an admission gate inherits the hazard.

## Break 3 — `claimed_coinbase_txid` is not reliably present

Two live bead-construction sites disagree about `transaction_ids`:

* `node/src/lib.rs:331-335` (`SwarmHandler::propagate_valid_bead`) fills it from
  `candidate_block.txdata`, so `[0]` is the coinbase txid.
* `node/src/stratum.rs:1276`, inside `validate_and_forward_upstream_share` (fn starts at
  `:1031`), constructs `transaction_ids: TxIdVec(Vec::new())` — **empty**.

Any fold-based check returns `FeeProofError::NoTransactions` for every bead produced by the
second path. The fold is therefore not even universally *evaluable*, let alone sound.

## Break 4 — the committed tx order does not survive a restart (verified blocker)

`db/schema.sql:31-35`:

```sql
CREATE TABLE IF NOT EXISTS Transactions (
      bead_id           INTEGER NOT NULL REFERENCES Bead(id),
      txid              BLOB,
      UNIQUE (bead_id, txid)
);
```

There is no ordinal column. The restore query at `db/db_handlers.rs:483-484` is
`SELECT bead_id, txid FROM Transactions WHERE bead_id IN (…)` with **no `ORDER BY`**, and
`:510-514` pushes rows into `transaction_ids.0` in whatever order SQLite returns. Committed
transaction order is lost on restart, and with it the canonical leaf order and the branch.
`UNIQUE (bead_id, txid)` additionally makes a repeated txid unstorable.

Consequence: *any* design whose correctness depends on the committed tx order is already
broken against the persistence layer. A node that restarts computes a different branch from
the same bead than it did before the restart. This is independent of the hypothesis and must
be fixed or designed around regardless. (Iteration 2 designs it away rather than fixing it:
canonical order becomes a *sort*, so nothing needs to be restored in order.)

A related, smaller defect in the same path: parents are restored from `ParentTimestamps`
ordered by `(child, parent)` i.e. by parent *row id* (`db_handlers.rs:517-523`), whereas
`propagate_valid_bead` sorts them by *hash* (`lib.rs:353`). Parent order therefore also
changes across a restart. It does not affect the bead hash (header only,
`utils/mod.rs:41-43`) but it does change the `CommittedMetadata` consensus encoding, so a
re-broadcast bead is byte-different from the original.

## Break 5 — there is no interface that can price a transaction this node did not template

This is the finding that matters most, and §2.7 dismisses it in one clause:

> a tx fee is objective (`inputs − outputs`) so any node holding tx + prevouts computes the
> same number

The premise "holding tx + prevouts" is exactly what differs between nodes. The full bitcoind
surface available to this node is `node/schema/mining.capnp:15-37`:

```
interface Mining:        isTestChain, isInitialBlockDownload, getTip, waitTipChanged,
                         createNewBlock, checkBlock, removeTxFromMempool
interface BlockTemplate: destroy, getBlockHeader, getBlock, getTxFees, getTxSigops,
                         getCoinbaseTx, getCoinbaseCommitment, getWitnessCommitmentIndex,
                         getCoinbaseMerklePath, submitSolution, waitNext
```

A repo-wide grep for `getrawtransaction`, `gettxout`, `get_raw_transaction`, `getmempool`
returns **nothing** in `node/`. There is no UTXO lookup, no raw-transaction fetch, and no
mempool query. The only fee source is `getTxFees` (`mining.capnp:29`,
`ipc/client.rs:444-458`), which returns fees for the transactions of *a template this
node's own bitcoind just built* — i.e. precisely route 3's limitation, now relocated from
the template cache into the fee oracle.

So with today's interfaces, `fee(t)` is a node-local value for any `t` outside this node's
own template, and `F_i = Σ fee(t)` over `S(X)` is node-local too. §0's "fee validation
becomes universal and cacheless" is **not achievable without extending the bitcoind
interface**. That is Unresolved Decision **D2**.

Two defects found in `getTxFees` handling while verifying this:

1. `ipc/client.rs:454-458` reads `List(Int64)` and casts each element `fee_value as u64`.
   Bitcoin Core's `CBlockTemplate::vTxFees[0]` holds `-nFees` for the coinbase slot, so if
   `getTxFees` returns the coinbase entry the cast yields `2^64 − nFees` and
   `lib.rs:224-228`'s `saturating_add` fold pins `fee_total_sats` at `u64::MAX`.
   `CommittedMetadata::consensus_decode` then rejects every such bead at the receiver
   (`committed_metadata/mod.rs:147-152`, `> MAX_MONEY`). **Unverified** — depends on whether
   Core's `BlockTemplate::getTxFees` includes the coinbase slot; the repo vendors only the
   schema. Must be confirmed before any of this is wired up, because it determines whether
   `fees[i]` aligns with `txdata[i]` or `txdata[i+1]`.
2. `lib.rs:224-228` uses `saturating_add` rather than `checked_add`, so an overflowing sum
   silently reports `u64::MAX` instead of failing. Same pattern as the already-noted
   `saturating_add` at `validate_fees.rs:331`.

## What survives, and why

`F_i` does not need to be proven by the bead, because `S(X)` is a pure function of the DAG
(§2.2) and a transaction's fee is a pure function of the transaction and the UTXO set at
`prev_blockhash` — both consensus objects. The verifier does not *check* the miner's number;
it *computes its own* and scores on that, discarding `fee_total_sats` as advisory. Once
`F_i` is derived rather than checked:

* no coinbase enters the fee path at any point → coinbase reconstruction (§2.8) is out of
  scope for fees — **§0 conclusion 1 holds**;
* nothing node-local enters the *value* of `F_i` → no cache — **conclusion 2 holds**;
* O1's global-key / node-local-value problem never arises — **conclusion 3 holds for `F_i`
  determinism**.

**Amended by Part 4**: this is necessary but not sufficient. Deriving `F_i` makes it
*deterministic*; it does not make it *bounded*. Because the miner chooses its delta and a
self-paying transaction's enormous fee is **real** rather than claimed, a correct oracle
prices it correctly and `F_i` inflates without any lie being told. Iteration 8 caps the
per-bead credit, which is what actually closes this.

But the fold that §0 rests on should be **deleted**, not built on. A check that every
participant passes for free is worse than no check: it reads as a cryptographic binding and
is not one. Iteration 2 replaces it with a direct state-key commitment, which does the one
job the fold can legitimately do (detect *honest* divergence so the node defers instead of
mis-scoring) at one hash instead of `d`, without needing the coinbase txid, and immune to
Breaks 2, 3 and 4.

## Residual exposure the hypothesis conceals

Once `F_i` is derived, **no miner needs to hold, validate or relay any transaction to be
credited its fees**. A free-rider with an empty mempool mines
`merkle_root = fold(garbage, B_derived)` and is credited the full `F_i` of the canonical
set. The fee path cannot detect this — there is nothing to detect, `F_i` is correct by
construction. What it breaks is (a) `A_i`'s economic meaning, and (b) the pool itself: such
a bead, if it meets the network target, is an unmineable block and the pool loses the whole
reward. Detecting it requires binding the bead to a *constructible* coinbase, which is the
roster path / O1.

So §0's "O1 is irrelevant to the fee path" is **true for `F_i` determinism and false for
`A_i`'s economic correctness**. Recorded as Unresolved Decision **D1**; not fixed here.

---

# Part 2 — Iterations

Baseline cost model used throughout, so the numbers are comparable:

| symbol | value | basis |
|---|---|---|
| `n` | 3000 | transactions in a mainnet template |
| `\|delta\|` | ≤ 5 | §2.1's 2–5 miner-chosen txs |
| bead rate | 1/s | assumed; scales linearly |
| epoch | 600 s ⇒ ~600 beads | one Bitcoin block |
| sha256d | ~120 ns per 64-byte compression | commodity x86 single core |
| IPC round-trip | ~50 µs | cap'n proto over a local socket, *unverified* |
| `B_base` | 312,500,000 sats | `edca/mod.rs:47` |

## Iteration 1 — Derive `F_i`; demote `fee_total_sats` to advisory

**Change.** `fee_total_sats` stops being an input to scoring. The verifier computes
`F_i = Σ_{t ∈ S(X)} fee(t)` from its own derivation of `S(X)` and scores on that. The
committed value stays on the wire and is compared only to raise a telemetry counter; a
mismatch is **neither a rejection nor a score change**.

**Resolves.** Priority 1's root defect ("checks miner data against miner data"). Route 1
(`verify_fee_commitment`, `validate_fees.rs:46-126`) and route 3
(`verify_fee_against_template`, `:484-522`) both become dead: there is nothing left for them
to check. `FeeVerdict::Unknown → F_i = 0` (`score.rs:66`) — the single most
determinism-hostile line in the tree, because it converts "I don't know" into a *number* —
is removed by construction.

**Breaks / newly exposes.**
1. The determinism problem relocates from "which set" to "which fee per transaction". `S(X)`
   is a DAG function and therefore safe; `fee(t)` is not, per Break 5. Iteration 3 is
   entirely about this.
2. `S(X)` becomes consensus-critical state that must survive restart ⇒ Break 4 must be
   resolved.
3. `CommittedFeeAmplifier` (`score.rs:33-42`) now reads an advisory field and is reachable
   from `EdcaState::from_braid` via `&dyn AmplifierSource`. It must be deleted or gated to
   `#[cfg(test)]`, or a mis-wiring pays miners whatever they claim.
4. The free-rider exposure named in Part 1.

**Cost.** Bead bytes: ±0. Hashes per bead at ingest: 0 (no fold). bitcoind round-trips per
bead: `|delta|` ≤ 5 at worst, 0 for the inherited part if memoised. Memory: one `S(X)` per
retained bead; stored naively as `Vec<Txid>` that is `3000 × 32 = 96 KB` per bead, so
**600 beads/epoch × 96 KB = 57 MB per epoch** and `100k beads × 96 KB = 9.6 GB` for a
full IBD — unacceptable, fixed in Iteration 5 by structural sharing. IBD: one pass, no extra
hashing beyond what Iteration 2 adds.

## Iteration 2 — Replace the fold with an explicit state-key commitment

**Change.** Delete the fold from the fee path. `CommittedMetadata` gains
`state_key: [u8;32]`, the miner's claim about *which* state it mined, and splits
`transaction_ids` into `coinbase_txid: Txid` plus `additional_tx_ids: TxIdVec`
(= `delta(X)`, length ≤ `MAX_DELTA`). The check becomes one comparison:

```
derived_state_key(X) == bead.committed_metadata.state_key
```

The full per-bead transaction list leaves the wire entirely: `S(X)` is reconstructed as
`⋃ S(parents) ∪ delta(X)` with the epoch base set (Iteration 4), so transmitting it is
redundant.

**Resolves.** Breaks 2, 3 and 4 at once — no tree shape, no dependence on
`transaction_ids[0]`, and no stored order, because canonical order becomes a *sort*
performed at load time rather than an order restored from the DB. Priority 4 collapses from
"pin a merkle leaf ordering" to "pin a digest preimage". Gives the verifier a *named* reason
to defer: the miner states which state it had, so "I am behind" is distinguishable from "you
are lying", which route 3 could never do (it only ever said `Unknown`).

**Breaks / newly exposes.**
1. The key is still unauthenticated (O7) — it is a hint, not a proof. That is all it ever
   was, and all it needs to be, because `F_i` no longer depends on it. Its only role is
   defer-vs-score.
2. Wire format break. Handled in Iteration 4 / spec (a).
3. A new node can no longer learn a bead's full tx set from the bead. It must replay deltas
   from the epoch base, which makes the epoch base a hard requirement (Iteration 4) rather
   than the loose end §2.4 leaves it as.
4. Dropping the tx list removes the `Transactions` table's reason to exist in its current
   form (spec (d)).

**Cost.** Bead bytes, mainnet template `n = 3000`:

| field | before | after |
|---|---|---|
| `transaction_ids` | `8 + 32·3000` = 96,008 B | — |
| `coinbase_txid` | — | 32 B |
| `additional_tx_ids` | — | `8 + 32·5` = 168 B |
| `state_key` | — | 32 B |
| `version` | — | 2 B |
| **net** | **96,008 B** | **234 B** |

A bead shrinks from ~96.2 kB to ~330 B total: a **~290× reduction**, and the largest single
effect in this design. IBD bead-sync bandwidth for 100k beads falls from ~9.6 GB to ~33 MB.
Hashes per bead at ingest: one sha256d over `4 + 32·|S|` bytes = 96,004 B ⇒ ~1,500
compressions ⇒ **~180 µs**; Iteration 5 keeps that at one digest per bead rather than per
parent. bitcoind round-trips: unchanged. Memory: unchanged from Iteration 1.

## Iteration 3 — A deterministic fee oracle (priorities 2 and 3)

This is the iteration that decides whether the design is viable.

**The key observation.** A transaction's fee is deterministic under a *weaker* condition
than §2.7 assumes. It does not need identical mempool views. It needs only:

* the **bytes of `t`** — self-authenticating against its txid, so any source will do; and
* the value of each prevout, which resolves in exactly one of two ways:
  * **in-state**: the prevout's txid is itself in `S(X)`. Then the output is read from that
    transaction's own bytes. This is the `IntermediateState` layering already implemented at
    `validate_fees.rs:284-298`, applied to a state instead of a block.
  * **confirmed**: the prevout is in the UTXO set at `prev_blockhash`. **The UTXO set at a
    fixed block is a consensus object**, identical on every node that has that block.

If the prevout is neither in `S(X)` nor in the UTXO set at `prev_blockhash`, the transaction
is invalid against the state and the bead is **permanently rejectable — deterministically**,
because both sets are consensus objects.

So `fee(t)` *is* deterministic. What varies between nodes is only **availability**: whether
this node holds `t`'s bytes, and whether its bitcoind has reached `prev_blockhash`. Both are
timing, not value. This yields the single invariant the whole design hangs on:

> **Every unavailability must produce a defer, never a number.**
> No code path may convert "I do not know `fee(t)`" into a partial sum, a zero, or a
> fallback. Those are payout forks.

That invariant kills, by name: `FeeBound::Undecided { computed_fees, missing }`
(`validate_fees.rs:308-315`) and its producer `verify_fee_bound` (`:320-354`), which returns
a partial sum and whose `saturating_add` at `:331` can even report `Proven` on overflow; and
`FeeVerdict::Unknown` mapped to `0` at `score.rs:66`.

**Change.** Introduce a `TxFeeOracle` with a three-way-plus-one result —
`Known(u64) | NotHeld | ChainBehind | Invalid(..)` — never a partial number. Back it with,
in order:

1. **own-template fees**: when this node's bitcoind builds a template, record
   `(epoch, txid) → fee` from `getTxFees` aligned to `getBlock`'s `txdata`
   (`ipc/client.rs:420-458`; `lib.rs:202-212` already deserialises that block). Free — the
   data is already fetched and currently only summed and thrown away.
2. **a persisted per-epoch fee table**, so a restart and an IBD do not re-price.
3. **a prevout query against bitcoind**, for transactions obtained from peers.
4. **a new p2p request** for raw transactions, so "I do not hold `t`" is recoverable rather
   than terminal. The existing `braidpool_protocol!` codec (`bead/mod.rs:68-125`) takes new
   variants cleanly: `BeadRequest::GetTransactions(TxIdVec)` /
   `BeadResponse::Transactions(..)`.

**Resolves.** Priority 2 (source + caching + unavailable-prevout behaviour) and priority 3
(determinism), *conditional on step 3 existing*.

**Breaks / newly exposes — and this is the blocker.** Step 3 has no implementation path in
the current tree. `mining.capnp` offers no UTXO or raw-transaction access (Break 5), so a
transaction fetched from a peer **cannot be priced at all**. Options, all requiring a
maintainer decision (**D2**):

| option | determinism | soundness | cost |
|---|---|---|---|
| (A) add a chain/UTXO interface (Core's `interfaces::Chain::findCoin`, or a JSON-RPC `gettxout` client) | full | full — fee is verified | new bitcoind dependency surface; ~1 round-trip per input |
| (B) peers serve `(tx, prevouts)` bundles | full | **asserted, not verified** — the server can lie about prevout values and no node can check | ~`32 + 40·inputs` B per tx |
| (C) the bead introducing `t` commits `fee(t)`; `F_i` sums committed fees | full (read from the DAG) | weakly sound; needs a per-tx fee cap or a miner claims 21 M BTC of fees | +8 B per delta entry |
| (D) abandon the amplifier: `F_i ≡ 0`, `A_i = B_base` | trivially full | n/a | zero; loses EDCA's fee-proportionality |

(A) is the only option that makes `fee(t)` *verified* rather than *asserted*. (C) is the
only one needing nothing from bitcoind; its attack is a miner inflating the committed fee of
a tx in its own delta. That inflation propagates to **every descendant bead**, including
competitors', so it largely cancels in the payout ratio — it is self-diluting, not free
money — but it is unbounded without a cap, so (C) requires `MAX_DELTA_FEE_SATS`. (D) is the
honest fallback if (A) is refused and (C) is judged too weak, and it should be named as a
live option rather than silently avoided.

**Cost of option (A), the recommended one.** Pricing a cold 3000-tx state at ~2.5 inputs
per tx = 7,500 prevout lookups ⇒ at 50 µs ⇒ **375 ms, once per epoch**. Steady state is
`|delta| × 2.5 ≈ 12.5` lookups per bead ⇒ **~0.6 ms per bead**, i.e. 0.06% of one core at
1 bead/s. With the own-template cache (source 1) most delta transactions are already priced
and the real figure is lower. IBD without a persisted fee table: 100k beads × 12.5 lookups
= 1.25 M round-trips ⇒ **~63 s**; with the table, ~0 for all but the current epoch. Fee
table size: `3000 × (32 + 32 + 8 + ~28 SQLite overhead)` ≈ **300 kB per epoch**, 144
epochs/day ⇒ **43 MB/day**, pruned to the EDCA retention window.

## Iteration 4 — Epoch base set, ingest placement, and the failure taxonomy (priority 5)

**Change — the epoch base set.** §2.4 says "reset at each new Bitcoin block" and §2.2 says
`S(X) = ⋃ S(parents) ∪ delta(X)`. Taken literally, `S` resets to `∅` and refills at
`|delta| ≤ 5` per bead, so a 3000-tx template needs ~600 beads ⇒ roughly a **full block
interval of near-empty templates at the start of every epoch**. That is not survivable and
§2.4 does not address it. Three candidates:

* reset to `∅` — rejected, as above;
* carry over "previous set minus what my bitcoind says confirmed" — rejected: the subtracted
  set is a node-local view, so the base diverges and with it every `F_i`;
* **carry over minus what the new block contains**: `S_base(E_new) = S_tip(E_prev) \ txs(B_new)`
  where `B_new` is the block whose hash is `prev_blockhash`. Both operands are consensus
  objects, so the base is deterministic. The only node-local part is *when* a node learns
  `B_new`, which is a defer condition because the epoch is named by the bead's own
  `prev_blockhash`. **Adopted.**

`S_tip(E_prev)` must be a single well-defined set, not per-tip. Define it as `S` of the
*union of all tips* at the moment `prev_blockhash` appears — but "the moment" is node-local.
Deterministic restatement: `S_base(E_new) = (⋃_{X ∈ A} S(X)) \ txs(B_new)` where `A` is the
set of beads in epoch `E_prev` that are ancestors of the first bead of `E_new`. This is
per-bead rather than global, which is slightly more work but needs no clock. **Unresolved
sub-point**, recorded as **D5**.

**Change — where the check runs.** Six real ingest sites call `Braid::extend`
(`braid/mod.rs:90`): `lib.rs:413`, `rpc_server.rs:338`, `main.rs:144`, `main.rs:1151`,
`main.rs:1595`, `audit.rs:683`, plus the recursive promotion at `braid/mod.rs:230`. The gate
must therefore be at or above `extend`, not duplicated per site.

It must **not** be inside `extend`, for two verified reasons: `extend` is synchronous and
returns `AddBeadStatus`, while fee resolution needs async I/O (bitcoind, p2p tx fetch); and
`extend` is re-entrant via `process_orphan_beads` (`braid/mod.rs:209-254`), which calls
`extend` recursively, so an async check inside would have to be re-entrant too.

Adopted shape: a two-phase async gate that wraps `extend`.

* **Phase A (sync, pure)** — parent presence (already there, `braid/mod.rs:110-120` ⇒
  `ParentsNotYetReceived`), epoch agreement, `delta ∩ S(parents) = ∅` (§2.3), `|delta| ≤
  MAX_DELTA`, no duplicate inside `delta`. All are pure functions of `(bead, DAG)`, so a
  permanent reject here is identical on every node.
* **Phase B (async)** — fetch any unheld tx in `delta`, price it, compute `F_i`, compare the
  derived state key.
* Only then `extend`. The bead must not enter `beads`/`cohorts` before `F_i` is known, or
  `EdcaState::from_braid` (`state.rs:65-155`) will score it with no fee.

**Failure taxonomy.**

| condition | verdict | why it is safe |
|---|---|---|
| a parent is missing | **defer** (orphan pool) | existing behaviour, `braid/mod.rs:117-118` |
| this node's bitcoind has not reached `prev_blockhash` | **defer** | node-local timing |
| a tx in `delta` is not held; fetch in flight | **defer** | node-local availability |
| a prevout is unresolvable because bitcoind is behind | **defer** | node-local timing |
| `delta ∩ S(parents) ≠ ∅` | **permanent reject** | pure DAG function |
| duplicate txid within `delta` | **permanent reject** | pure |
| `\|delta\| > MAX_DELTA` | **permanent reject** | pure |
| `Σ` committed delta fees `> MAX_DELTA_FEE_SATS` (option C only) | **permanent reject** | pure |
| a delta tx spends an outpoint absent from both `S(X)` and UTXO@`prev_blockhash`, **and** bitcoind is at or past `prev_blockhash` | **permanent reject** | both sets are consensus at a fixed block; the bitcoind-synced precondition is what makes it deterministic rather than a race |
| same, but bitcoind is behind | **defer** | the two cases are indistinguishable without the chain |
| two delta txs in one cohort spend the same outpoint | **permanent reject of one**, by a pinned tiebreak | pure given `S(X)` — but the rule is unspecified (O3), see **D3** |
| committed `fee_total_sats ≠` derived `F_i` | **accept, score on derived `F_i`**, log + misbehaviour counter | an honest miner whose bitcoind priced differently must not be rejected |
| committed `state_key ≠` derived key | **defer while any ancestor is unsettled; then accept with derived `F_i`** and a counter — never reject | rejection must be a pure-DAG decision; see **D4** |

Every permanent reject above is a pure function of `(bead, DAG, chain@prev_blockhash)`, so
**an honest bead is never permanently rejected and no two honest nodes disagree about a
rejection**, which is priority 5's requirement.

**Resolves.** Priority 5 completely; the epoch-base gap in §2.4; §2.9's "defer, don't
reject" made concrete per condition.

**Breaks / newly exposes.** The orphan pool now parks beads for two distinct reasons
(missing parents, unresolved fees) and `orphan_beads: Vec<Bead>` (`braid/mod.rs:36`) is an
unbounded `Vec` with a linear retry scan (`braid/mod.rs:209-254`), with no eviction and no
cap. A peer can grow it without limit by sending beads referencing unknown transactions.
Needs a bound and an eviction policy before this ships. Also `process_orphan_beads` recurses
once per promotion (`:238`), so a long parked chain recurses to its depth — a stack hazard
at a few thousand beads.

**Cost.** Phase A: `|delta| ≤ 5` set membership tests against `S(parents)` ⇒ sub-µs. Phase
B: as Iteration 3. Latency added to ingest: ~0.6 ms typical, up to one p2p round-trip
(~100 ms LAN / ~300 ms WAN, *unverified*) when a delta tx must be fetched. At 1 bead/s that
is not a throughput constraint.

## Iteration 5 — Incremental state representation (making Iteration 1's memory viable)

**Change.** `S(X)` is held as an **immutable ordered set with structural sharing** (a
persistent balanced tree: `im::OrdSet<Txid>` or `rpds::RedBlackTreeSet<Txid>`), not a
`Vec<Txid>`. A child's state is its parents' states unioned plus `|delta| ≤ 5` inserts,
sharing all untouched nodes with the parents. In-order traversal yields the canonical sort
for the digest at no extra cost, so no sort step exists.

**Resolves.** Iteration 1's 9.6 GB. Also removes the digest's dependence on any stored
order, completing the Break 4 fix.

**Breaks / newly exposes.** A union of two parents' sets is `O(|smaller| · log)` in the
worst case, not `O(|delta|)`, so a bead with many parents on divergent states is more
expensive than a linear-chain bead. With parents typically on near-identical states the
union is nearly free (shared subtrees short-circuit), but a merge bead after a split is not.
Needs measurement. Adds a dependency (`im` or `rpds`); neither is currently in the tree
(*unverified* — not checked against `Cargo.toml`).

**Cost.** Per bead: `|delta| × log2(3000) ≈ 5 × 11.5 ≈ 60` new tree nodes × ~48 B ⇒
**~2.9 kB per bead** instead of 96 kB — a **33× reduction**. One epoch of 600 beads ⇒
**1.7 MB** resident. States are retained only for beads whose descendants may still be
validated (one epoch); older beads keep only their persisted `F_i`, so the figure does not
grow with history. Digest: still one sha256d over `4 + 32·|S|` bytes per bead ⇒ ~180 µs,
= **18 s of hashing for a 100k-bead IBD**, on top of ~63 s of prevout lookups (or ~0 with
the persisted fee table). Total fee-path IBD overhead: **~20 s warm, ~80 s cold, for 100k
beads.**

---

# Part 3 — Converged Specification

## (a) `CommittedMetadata` wire layout

### Current layout (verified)

Fields `node/src/committed_metadata/mod.rs:66-82`; `Encodable` `:103-122`; `Decodable`
`:124-165`. Encoding is strictly positional, hand-written, with no tag and no outer length
prefix. `CommittedMetadata` is embedded in `Bead` by `impl_consensus_encoding!`
(`bead/mod.rs:48`) and `Bead` in `Beads` by `impl_vec_wrapper!` (`:23`).

| # | field | type | encoded as |
|---|---|---|---|
| 1 | `transaction_ids` | `TxIdVec` | `u64` count + `32·n` |
| 2 | `parents` | `Vec<BeadHash>` | rust-bitcoin `Vec` (CompactSize + 32 each) |
| 3 | `parent_bead_timestamps` | `TimeVec` | `u64` count + `u32` each |
| 4 | `payout_address` | `String` | CompactSize + UTF-8 |
| 5 | `start_timestamp` | `Time` | `u32` |
| 6 | `comm_pub_key` | `PublicKey` | `Vec<u8>`: CompactSize + 33 |
| 7 | `min_target` | `CompactTarget` | `u32` |
| 8 | `weak_target` | `CompactTarget` | `u32` |
| 9 | `miner_ip` | `String` | CompactSize + UTF-8 |
| 10 | `fee_total_sats` | `u64` | `u64`, decode rejects `> MAX_MONEY` (`:147-152`) |

### Proposed layout

```
 #  field                      type             bytes        notes
 1  version                    u16              2            MUST be 2; decode rejects anything else
 2  parents                    Vec<BeadHash>    1 + 32·p     CompactSize; p <= MAX_PARENTS
 3  parent_bead_timestamps     TimeVec          8 + 4·p      count MUST equal p
 4  payout_address             String           1 + len      len <= MAX_ADDR_LEN
 5  start_timestamp            u32              4
 6  comm_pub_key               [u8; 33]         33           fixed width, no length prefix
 7  min_target                 CompactTarget    4
 8  weak_target                CompactTarget    4
 9  miner_ip                   String           1 + len      len <= 45 (INET6_ADDRSTRLEN)
10  coinbase_txid              Txid             32           replaces transaction_ids[0]
11  additional_tx_ids          TxIdVec          8 + 32·d     d = |delta| <= MAX_DELTA
12  state_key                  [u8; 32]         32           epoch-scoped key the miner claims
13  fee_total_sats             u64              8            ADVISORY ONLY; not a scoring input
```

Total for `p = 3`, `d = 5`, 42-byte address, 15-byte IP: **2 + 97 + 20 + 43 + 4 + 33 + 4 +
4 + 16 + 32 + 168 + 32 + 8 = 463 B**, against ~96.5 kB today at `n = 3000`.

Encode and decode MUST follow this order exactly. Rules a second implementation must match
byte for byte:

1. **`version` first**, so a decoder can dispatch before allocating anything.
2. `additional_tx_ids` MUST be **strictly ascending** by `Txid::to_byte_array()` on the
   wire — i.e. the canonical order of (a)'s key, not insertion order. Decode MUST reject
   non-ascending or repeated entries. This makes the encoding canonical: one delta has
   exactly one serialisation, which matters because the DB round-trip (Break 4) otherwise
   re-emits a byte-different bead.
3. Decode MUST bound **every** length prefix before allocating. The current
   `TxIdVec::consensus_decode` reads a `u64` and calls `Vec::with_capacity(len as usize)`
   (`committed_metadata/mod.rs:51-53`) with no bound — **an allocation-DoS reachable from
   `BeadCodec::read_request` (`bead/mod.rs:140-148`) with 8 crafted bytes**. Same pattern in
   `TimeVec::consensus_decode` (`:27-29`). Fix regardless of this design.
4. `parent_bead_timestamps.len()` MUST equal `parents.len()`; today nothing checks it and
   `resolve_parents` (`braid/mod.rs:255-276`) reads only `parents`, so a mismatch passes
   silently.
5. `fee_total_sats` keeps its `> MAX_MONEY` rejection, but as a sanity bound on a field
   nothing consumes for scoring.

### Backward compatibility, and whether a version field is needed

**Decision: add `version: u16`, and accept a flag-day break.**

The compatibility question has a sharper answer than it looks. The two serialisation paths
are not the same:

* **Wire** (p2p) uses `Encodable`/`Decodable` — `BeadCodec` at `bead/mod.rs:140-194`. It is
  positional with no tags, so **no version field can make an old decoder read a new
  encoding**. Put `u16 version` first and an old peer reads those 2 bytes as the low half of
  `transaction_ids`' `u64` count and then allocates on garbage. Compatibility here is
  impossible by construction; the only question is whether the failure is *diagnosable*.
* **DB/JSON** uses serde (`db_handlers.rs:200-218` writes `json_extract`-able JSON). The
  live `#[serde(default)]` on `fee_total_sats` (`committed_metadata/mod.rs:81`) therefore
  concerns **rows written before the column existed**, not peers. It should stay — it is
  harmless and it does cover old rows — but it must not be read as a wire-compatibility
  story. It is not one.

So `version` buys forward dispatch and a clean "peer speaks v1, I speak v2" diagnostic
instead of a garbage allocation, not backward compatibility. That is worth 2 bytes.

The break itself is acceptable **now and not later**: `fee_total_sats` was added on this
branch (`7bff1e3`), nothing validates it, `validate_fees.rs` has zero callers, and
`EdcaState::from_braid` has zero callers (verified: the only match for `from_braid` in the
tree is its own definition at `state.rs:65`). There is no deployed network to break. The DB
needs a migration (spec (d)), not a compatibility shim.

## (b) Rust types and signatures

**Signatures and doc comments only. No bodies. No `.rs` file is modified by this document.**

### New module `node/src/edca/cmempool.rs`

```rust
use crate::bead::Bead;
use crate::braid::Braid;
use crate::utils::BeadHash;
use bitcoin::{BlockHash, Txid};
use std::sync::Arc;

/// Transaction ids in canonical order: strictly ascending by the 32-byte
/// internal serialisation, `Txid::to_byte_array()`.
///
/// This is **not** display order. `Txid`'s `Display` prints the reversed
/// (big-endian) form, and sorting by the displayed hex gives a different
/// order. `Txid: Ord` in rust-bitcoin compares the internal array, so
/// `Vec<Txid>::sort_unstable()` is the correct primitive and a second
/// implementation must sort the same bytes.
///
/// Invariants, upheld by construction and re-checked on decode:
/// strictly ascending, therefore no duplicates.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CanonicalTxids(/* private */);

impl CanonicalTxids {
    /// Builds the canonical ordering of `txids`.
    ///
    /// # Errors
    /// [`CmempoolError::DuplicateTxid`] if `txids` repeats an entry. A
    /// duplicate is an error and never silently deduplicated: in a delta it
    /// is a protocol violation, and in a state it cannot occur under the
    /// §2.3 disjointness rule, so seeing one means a bug upstream.
    pub fn new(txids: impl IntoIterator<Item = Txid>) -> Result<Self, CmempoolError>;

    /// Returns the txids in canonical order.
    pub fn as_slice(&self) -> &[Txid];

    /// Returns how many transactions are in the set.
    pub fn len(&self) -> usize;

    /// Returns whether the set is empty.
    pub fn is_empty(&self) -> bool;
}

/// The epoch-scoped identity of a committed-mempool state.
///
/// Derivable by any node from the DAG alone, identical everywhere, and
/// immune to grinding: forcing a different state to present the same key
/// needs a sha256d collision.
///
/// Definition, which two implementations must agree on byte for byte:
///
/// ```text
/// set_digest = SHA256d( u32_le(|S|) || t_1 || t_2 || ... || t_n )
/// state_key  = SHA256d( prev_blockhash.to_byte_array() || set_digest )
/// ```
///
/// where `t_i` are `Txid::to_byte_array()` in [`CanonicalTxids`] order. The
/// `u32_le` count prefix pins `|S|` so no two sets share a preimage; the
/// outer hash scopes the key to one Bitcoin block (§2.4), so identical
/// transaction sets on different `prev_blockhash` values are incomparable.
/// The empty set is `SHA256d(00 00 00 00)` — defined, not a special case.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct StateKey([u8; 32]);

impl StateKey {
    /// Computes the key of `members` on `epoch`.
    pub fn of(epoch: BlockHash, members: &CanonicalTxids) -> Self;

    /// Returns the raw digest.
    pub fn to_byte_array(self) -> [u8; 32];
}

/// The committed-mempool state a bead was mined on, with its derived fee
/// total.
///
/// `members` is an immutable ordered set with structural sharing, so a
/// child's state shares every untouched subtree with its parents'. A
/// `Vec<Txid>` here would cost ~96 kB per bead at a 3000-transaction state;
/// sharing brings that to ~2.9 kB (Iteration 5). In-order traversal yields
/// [`CanonicalTxids`] order directly, so no sort step exists.
#[derive(Debug, Clone)]
pub struct CmempoolState {
    /// The Bitcoin block this state is scoped to, equal to the bead's
    /// `block_header.prev_blockhash`.
    pub epoch: BlockHash,
    /// Members of `S(X)`, structurally shared with the parents' states.
    pub members: PersistentTxidSet,
    /// `StateKey::of(epoch, canonical(members))`, cached.
    pub key: StateKey,
    /// `F_i`: the sum of `fee(t)` over `members`, in satoshis. The value the
    /// amplifier scores on. Derived by this node; never read from the bead.
    pub fee_total_sats: u64,
}

/// An immutable ordered set of txids with O(1) sharing on clone.
///
/// Thin alias over a persistent balanced tree (`im::OrdSet<Txid>` or
/// `rpds::RedBlackTreeSet<Txid>`). Named here so the dependency choice does
/// not leak into every signature.
pub type PersistentTxidSet = /* persistent ordered set of Txid */;

/// Protocol limits on a bead's delta. Consensus parameters: every node must
/// use the same values or permanent rejections diverge.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeltaLimits {
    /// Maximum `|delta(X)|`, i.e. `additional_tx_ids.len()`. §2.1 says 2..5,
    /// so 5.
    pub max_delta_len: usize,
    /// Maximum total fee a single bead's delta may contribute, in satoshis.
    /// Bounds the fee-stuffing advantage one bead can buy over a same-cohort
    /// competitor. Only load-bearing under option (C) of Iteration 3.
    pub max_delta_fee_sats: u64,
}

/// Per-bead derived state, memoised over the DAG, for one epoch.
///
/// Rebuildable after a restart from the persisted deltas and fee table; it
/// is a cache of a DAG function, never a source of truth, so it can be
/// dropped and recomputed without changing any `F_i`.
#[derive(Debug)]
pub struct CmempoolIndex {
    /* epoch, base state, by_bead: HashMap<BeadHash, Arc<CmempoolState>> */
}

impl CmempoolIndex {
    /// Creates an index for `epoch` whose beads inherit from `base`.
    ///
    /// `base` is `S_base(epoch)` per Iteration 4: the states of the
    /// previous epoch's boundary beads, minus the transactions confirmed in
    /// the block named by `epoch`.
    pub fn new(epoch: BlockHash, base: Arc<CmempoolState>) -> Self;

    /// Returns the derived state of `bead`, or `None` if it has not been
    /// validated in this epoch.
    pub fn state_of(&self, bead: &BeadHash) -> Option<&Arc<CmempoolState>>;

    /// Derives `S(X)` and `F_i` for `bead` from its parents' states.
    ///
    /// `S(X) = union of parents' members, plus delta(X)`. Pure except for
    /// `fees`, which supplies `fee(t)` for the delta; inherited members are
    /// already priced into the parents' `fee_total_sats`, so this prices
    /// only `|delta| <= max_delta_len` transactions per bead.
    ///
    /// # Errors
    /// * [`CmempoolError::ParentNotDerived`] — a parent has no state yet;
    ///   the caller must defer, not reject.
    /// * [`CmempoolError::DeltaOverlapsState`] — §2.3 violated. Permanent.
    /// * [`CmempoolError::DeltaTooLong`] / `DeltaFeeCapExceeded` — permanent.
    /// * [`CmempoolError::EpochMismatch`] — the bead's `prev_blockhash` is
    ///   not this index's epoch. Permanent for this index; the caller routes
    ///   the bead to the right epoch or defers.
    /// * [`CmempoolError::FeeUnavailable`] — the oracle answered `NotHeld`
    ///   or `ChainBehind`. **The caller must defer.** It must never
    ///   substitute a partial sum or zero.
    /// * [`CmempoolError::FeeOverflow`] — `checked_add`, never saturating.
    pub fn derive(
        &self,
        braid: &Braid,
        bead: &Bead,
        fees: &dyn TxFeeOracle,
        limits: &DeltaLimits,
    ) -> Result<Arc<CmempoolState>, CmempoolError>;

    /// Records a derived state so descendants and the amplifier can read it.
    pub fn insert(&mut self, bead: BeadHash, state: Arc<CmempoolState>);

    /// Replaces the epoch, dropping every memoised state.
    ///
    /// Called when a bead arrives on a new `prev_blockhash`. States from the
    /// old epoch are not comparable with the new one (§2.4), so retaining
    /// them would be a correctness hazard rather than a saving.
    pub fn reset_epoch(&mut self, epoch: BlockHash, base: Arc<CmempoolState>);
}
```

### The fee oracle

```rust
/// What this node can say about one transaction's fee.
///
/// The variants that are not `Known` carry **no number**. That is the
/// determinism invariant of the whole design: an unavailable fee must
/// propagate as a defer, never as a partial sum, a zero, or a fallback.
/// Two honest nodes that both answer `Known` answer the same number,
/// because a fee is a pure function of the transaction and the UTXO set at
/// the epoch, both consensus objects.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FeeLookup {
    /// The fee, in satoshis. Deterministic.
    Known(u64),
    /// This node does not hold the transaction's bytes. **Defer.**
    /// Node-local availability; recoverable by fetching it from a peer.
    NotHeld,
    /// This node's bitcoind has not reached the epoch's block, so the UTXO
    /// set at that block is not queryable. **Defer.** Node-local timing.
    ChainBehind,
    /// The transaction provably cannot be valid at this epoch: an input
    /// spends an outpoint absent from both the epoch's UTXO set and the
    /// state. Deterministic given a synced chain, so **permanent reject**.
    Unspendable {
        /// The outpoint that does not exist at this epoch.
        outpoint: bitcoin::OutPoint,
    },
    /// Inputs sum below outputs, or values leave the money range.
    /// Deterministic, so **permanent reject**.
    Invalid,
}

/// A deterministic per-transaction fee source for one epoch.
///
/// Implementations resolve, in order: this node's own template fees
/// (recorded from `getTxFees`, `ipc/client.rs:444-458`); the persisted
/// per-epoch fee table; prevout resolution against the state itself for
/// in-state parents; and a chain query for confirmed prevouts.
///
/// An implementation MUST NOT guess. Returning `Known` with an estimate is
/// a payout fork.
pub trait TxFeeOracle {
    /// Returns what this node knows about `txid`'s fee at `epoch`.
    ///
    /// `in_state` lets the oracle resolve a prevout created by another
    /// transaction already in `S(X)` without a chain query, mirroring the
    /// in-block layering of `IntermediateState`
    /// (`edca/validate_fees.rs:284-298`).
    fn fee_sats(
        &self,
        txid: &Txid,
        epoch: BlockHash,
        in_state: &PersistentTxidSet,
    ) -> FeeLookup;
}

/// A fee oracle over this node's own templates plus a persisted fee table.
///
/// Fees recorded here cost nothing: `lib.rs:202-212` already deserialises
/// the template's full block and `ipc/client.rs:444-458` already fetches
/// `getTxFees`; today the per-transaction values are summed once
/// (`lib.rs:224-228`) and discarded.
#[derive(Debug, Default)]
pub struct TemplateFeeOracle {
    /* epoch -> (txid -> fee_sats), plus a handle for chain queries */
}
```

### Ingest entry point

```rust
/// Why a bead could not be validated yet, and must be retried rather than
/// rejected.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DeferReason {
    /// A parent is not in the DAG. Existing `Braid::extend` behaviour
    /// (`braid/mod.rs:110-120`).
    ParentMissing(BeadHash),
    /// A parent is in the DAG but has no derived state yet.
    ParentNotDerived(BeadHash),
    /// This node lacks the bytes of a transaction in the bead's delta.
    TransactionNotHeld(Txid),
    /// This node's bitcoind has not reached the bead's `prev_blockhash`.
    ChainBehind(BlockHash),
    /// The derived key disagrees with the claim while an ancestor is still
    /// unsettled, so divergence cannot yet be distinguished from lag.
    StateKeyMismatchPending {
        /// What this node derived.
        derived: StateKey,
        /// What the bead claims.
        claimed: StateKey,
    },
}

/// The outcome of the fee gate for one bead.
#[derive(Debug)]
pub enum FeeIngest {
    /// `F_i` is known; the bead may enter the DAG.
    Accepted {
        /// The derived state, to be memoised for descendants.
        state: Arc<CmempoolState>,
        /// `F_i`, in satoshis. Equal to `state.fee_total_sats`; repeated so
        /// the caller can persist it without reaching into the state.
        fee_total_sats: u64,
        /// Whether the bead's advisory `fee_total_sats` matched `F_i`. A
        /// `false` here is a misbehaviour signal only: it never changes the
        /// score and never rejects the bead, because an honest miner whose
        /// bitcoind priced a transaction differently must still be scored.
        claim_matched: bool,
        /// Whether the bead's `state_key` matched the derived key. Same
        /// status as `claim_matched`: a signal, not a verdict.
        key_matched: bool,
    },
    /// Retry later. The bead goes to the orphan pool and must not enter
    /// `beads` or `cohorts`.
    Defer(DeferReason),
    /// Reject permanently. Every variant reachable here is a pure function
    /// of `(bead, DAG, chain@prev_blockhash)`, so every honest node reaches
    /// the same verdict and an honest bead never lands here.
    Reject(CmempoolError),
}

/// Validates a bead's fees and derives `F_i`, before it enters the DAG.
///
/// This is the ingest gate. It must run **before** `Braid::extend`
/// (`braid/mod.rs:90`), because a bead inside `beads`/`cohorts` without a
/// derived `F_i` would be scored by `EdcaState::from_braid`
/// (`state.rs:65-155`) with no fee.
///
/// It cannot live *inside* `extend`: `extend` is synchronous and returns
/// `AddBeadStatus`, while fee resolution needs async I/O; and `extend` is
/// re-entrant through `process_orphan_beads` (`braid/mod.rs:209-254`).
///
/// All six ingest sites must be migrated to call this first: `lib.rs:413`,
/// `rpc_server.rs:338`, `main.rs:144`, `main.rs:1151`, `main.rs:1595`,
/// `audit.rs:683`.
///
/// Phase A (synchronous, pure): epoch agreement, parent states present,
/// `delta ∩ S(parents) = ∅`, `|delta| <= max_delta_len`, delta canonical and
/// duplicate-free. Phase B (asynchronous): price the delta, sum `F_i`,
/// compare the derived key.
pub async fn validate_bead_fees(
    braid: &Braid,
    index: &CmempoolIndex,
    bead: &Bead,
    fees: &dyn TxFeeOracle,
    limits: &DeltaLimits,
) -> FeeIngest;
```

### Plugging into the existing `AmplifierSource`

`AmplifierSource::fee_sats(&self, bead: &Bead) -> Result<u64, EdcaError>` (`score.rs:9-13`)
takes only a `&Bead`, with no bead hash, so an implementation that looks up a derived state
needs the network to compute the hash. `Braid` carries it (`compute_bead_hash`,
`braid/mod.rs:72-74`), so the amplifier holds `&Braid`. The trait does **not** need to
change.

```rust
/// [`AmplifierSource`] that reads the `F_i` derived at ingest.
///
/// §2.10: validate once at ingest, score from storage. The amplifier never
/// re-derives, so states need not be retained for the whole EDCA scoring
/// window — only for the current epoch.
pub struct DerivedFeeAmplifier<'a> {
    index: &'a CmempoolIndex,
    braid: &'a Braid,
}

impl<'a> DerivedFeeAmplifier<'a> {
    /// Scores beads from `index`, resolving bead hashes through `braid`.
    pub fn new(index: &'a CmempoolIndex, braid: &'a Braid) -> Self;
}

impl AmplifierSource for DerivedFeeAmplifier<'_> {
    /// Returns the `F_i` derived for `bead` at ingest.
    ///
    /// # Errors
    /// [`EdcaError::FeeNotDerived`] if the index has no entry. This is an
    /// **error, not a zero**. A bead in the DAG without a derived `F_i`
    /// violates the ingest gate's invariant, so failing the whole state
    /// build is correct; returning 0 would be `score.rs:66`'s
    /// `Unknown => 0` fork reappearing under a new name. `from_braid`
    /// already propagates with `?` at `state.rs:107`.
    fn fee_sats(&self, bead: &Bead) -> Result<u64, EdcaError>;
}
```

A new `EdcaError` variant is required:

```rust
/// A bead in the braid has no derived `F_i`, so the state cannot be scored.
/// Means the ingest gate was bypassed, or the index was lost and not
/// rebuilt after a restart.
FeeNotDerived {
    /// The bead with no derived fee total.
    bead: BeadHash,
},
```

### Persistence

```sql
-- Bead gains two derived columns, so a restart does not re-price.
ALTER TABLE Bead ADD COLUMN state_key BLOB;                  -- 32 B
ALTER TABLE Bead ADD COLUMN derived_fee_total_sats INTEGER;  -- F_i

-- The bead's delta replaces the full transaction list. No ordinal column is
-- needed: canonical order is a sort (CanonicalTxids), not a stored order,
-- which is what closes Break 4.
CREATE TABLE IF NOT EXISTS BeadDelta (
    bead_id INTEGER NOT NULL REFERENCES Bead(id),
    txid    BLOB NOT NULL,
    UNIQUE (bead_id, txid)
);

-- Per-epoch transaction fees, so IBD prices only the current epoch.
-- ~300 kB per epoch, ~43 MB/day; prune to the EDCA retention window.
CREATE TABLE IF NOT EXISTS TxFee (
    epoch    BLOB NOT NULL,
    txid     BLOB NOT NULL,
    fee_sats INTEGER NOT NULL CHECK (fee_sats >= 0),
    PRIMARY KEY (epoch, txid)
);
```

The existing `Transactions` table (`db/schema.sql:31-35`) and its restore path
(`db_handlers.rs:483-515`) are deleted with the full tx list.

## (c) Worked numeric example

All digests below are **real** — computed with the spec's exact preimages
(`SHA256d(u32_le(count) || txids…)`, then `SHA256d(prev_blockhash || set_digest)`) and
reproducible from the table alone.

### Setup

`epoch` = `prev_blockhash` `P` = `aa…aa` (32 × 0xaa), internal byte order.
Transactions, each txid being a 32-byte repeat of one byte so canonical order is obvious:

| tx | txid (internal, 32 B) | `fee(t)` sats |
|---|---|---|
| `t1` | `11…11` | 1,000 |
| `t2` | `12…12` | 2,000 |
| `t3` | `13…13` | 500 |
| `t4` | `14…14` | 700 |
| `t5` | `15…15` | 300 |
| `t6` | `16…16` | 900 |

Canonical order is `t1 < t2 < t3 < t4 < t5 < t6` by ascending first byte.
`S_base(P)` = `{t1, t2}`, carried from the previous epoch minus the transactions confirmed
in `P` (Iteration 4). `B_base` = 312,500,000 (`edca/mod.rs:47`).
`MAX_DELTA` = 5.

### DAG — 6 beads over 3 cohorts

```
 cohort 0       cohort 1            cohort 2         cohort 3
    G      →     A  (d={t3})   →      C (d={t5})  →   D (d={t6})
                 B  (d={t4})   ^                      F (d={})
                                                      E (d={t4}) <- REJECTED
```

* `G`: epoch-boundary bead, `S(G) = S_base = {t1,t2}`, `d(G) = {}`. Cohort 0 = `{G}`.
* `A`: parents `{G}`, `d(A) = {t3}`
* `B`: parents `{G}`, `d(B) = {t4}` — concurrent with `A`, so cohort 1 = `{A, B}`
* `C`: parents `{A, B}`, `d(C) = {t5}` — sees both, cohort 2 = `{C}`
* `D`: parents `{C}`, `d(D) = {t6}`
* `F`: parents `{C}`, `d(F) = {}` — an empty delta is legal. Concurrent with `D`, so
  cohort 3 = `{D, F}`.
* `E`: parents `{C}`, `d(E) = {t4}` — **permanently rejected**:
  `d(E) \cap S(C) = {t4} != {}`, violating §2.3. A pure DAG function, so every node
  reaches the same verdict and no honest bead can land here.

### Derived states, keys, `F_i` and `A_i`

| bead | `S(X)` canonical | \|S\| | preimage | `set_digest` (SHA256d) | `F_i` | `A_i = B_base + F_i` |
|---|---|---|---|---|---|---|
| `G` | `t1 t2` | 2 | 68 B | `ece548fbf4acfafbb94c1ddd8a0916ad71e875d38c8b5958034e80d05fd72c90` | 3,000 | 312,503,000 |
| `A` | `t1 t2 t3` | 3 | 100 B | `9bc3ae40f3866aed882fe1b972853a9a6dac10df07e18516e1c4d9e7514a0a5a` | 3,500 | 312,503,500 |
| `B` | `t1 t2 t4` | 3 | 100 B | `2913f592c8618749f79c277596e8d79c5fdd42ac99c23bf5389952820c8fe537` | 3,700 | 312,503,700 |
| `C` | `t1 t2 t3 t4 t5` | 5 | 164 B | `c7f1ebc1a4e88b71b7cf8bfb9acdd55bb50e5dc35c314925db446b1b11e93c76` | 4,500 | 312,504,500 |
| `D` | `t1 … t6` | 6 | 196 B | `36b713097c530f9aa716136cbf10499ad0a7b7a8c60629cfa00d6b0efb8736c0` | 5,400 | 312,505,400 |
| `F` | `t1 t2 t3 t4 t5` | 5 | 164 B | `c7f1ebc1a4e88b71b7cf8bfb9acdd55bb50e5dc35c314925db446b1b11e93c76` | 4,500 | 312,504,500 |

Epoch-scoped `state_key = SHA256d(P || set_digest)` — the value each bead carries in field
12:

| bead | `state_key` |
|---|---|
| `G` | `bb303134a66321f95a2df08c6c1fdc16e02a1c248383b30c91374607d3353af5` |
| `A` | `0aa20be3206989dc3d3cf58c6d5dfebe6a321a9868e4028f88cb4a2c4f758778` |
| `B` | `64bffeeac49a1b6d2b2686f55a4e642db93a3cbd83c7f50203e4befb68c54c4f` |
| `C` | `2b9c5dc4511a8ee9cb39004a13fba558758951ea5389c527933eca976748c374` |
| `D` | `f3e740acdaaf3949a188d8ca32910885a1d15e6364fdc5ace6d69f400a649c15` |
| `F` | `2b9c5dc4511a8ee9cb39004a13fba558758951ea5389c527933eca976748c374` |

`C`'s merge is the load-bearing case: `S(C) = S(A) \cup S(B) \cup {t5} =
{t1,t2,t3,t4,t5}`, so `F_C = 1000+2000+500+700+300 = 4,500`. Note that the union, not the
sum, is what merges: `t1` and `t2` are counted once although both parents carry them. A
`F_C = F_A + F_B + 300` implementation would double-count the inherited set and is the most
likely implementation error in this design.

`F` has an empty delta, so `S(F) = S(C)` and `F` carries *the same `state_key` as `C`*
(`2b9c5dc4…`). That is correct and expected: the key identifies a state, not a bead. An
implementation must not assume keys are unique per bead, and must not use the key as a
bead-level index.

### Two observations the example makes concrete

1. **`F_i` is not cohort-uniform.** `A` and `B` are in the same cohort with `F_A = 3,500`
   and `F_B = 3,700`. A miner can raise its own `F_i` relative to a same-cohort competitor
   by introducing a high-fee transaction. The advantage is bounded by
   `MAX_DELTA × max_delta_fee_sats / B_base`: at a 1,000,000-sat cap and 5 transactions
   that is `5,000,000 / 312,500,000` = **+1.6% on `A_i`**. Without `max_delta_fee_sats` it
   is unbounded, since the only existing check is `fee_total_sats <= MAX_MONEY`
   (`committed_metadata/mod.rs:147-152`), which permits a single claimed fee of 21 M BTC.
2. **The fold adds nothing** (Part 1, Break 1), demonstrated on `S(C)`. Leaves are
   `[coinbase] ++ [t1,t2,t3,t4,t5]`, 6 leaves, branch depth 3:

   ```
   derived branch B = [ 1111…11,
                        3df5a631fb114f37f8ee2446bcaa7c5a0db1bdb6218162808b72b3df9145a512,
                        c95487b944215e1c9df6d18cf2edfabb89ae0be580ea86be15855afcc417fe21 ]

   honest coinbase c0…c0 : fold = 8b1d740d01b13c4a13ed7478e0b450b12c3a00f777f736a8fb9669202738404a
                                 (= the real merkle root, as it must)
   garbage  deadbeef…    : fold = 05925ed60504606ae0d6b33cbf1e1322d2e24f4436b032b0e429ee16c1b82b39
   ```

   The attacker publishes `coinbase_txid = deadbeef…`, writes the second digest into
   `header.merkle_root`, mines, and the fold verifies. It holds no transactions. The
   `state_key` check, by contrast, would reveal nothing about honesty either — but it is
   one hash rather than three, needs no coinbase txid, and reports *which* state the miner
   claimed, which is the only thing a verifier can act on.

## (d) Migration from `validate_fees.rs`

`node/src/edca/validate_fees.rs` is 620 lines with **zero callers outside its own module
and the `pub use` block at `edca/mod.rs:16-21`** (verified by grep across `node/src`;
`node/tests` does not exist). So the migration is unconstrained by callers. Per public item:

### Survives, unchanged or re-homed

| item | lines | disposition |
|---|---|---|
| `transaction_fee` | 193-238 | **Survives**, moves to the fee-oracle module. This is the one correct, reusable primitive in the file: `inputs − outputs` with `checked_add`, `checked_sub`, a money-range filter, and `MissingPrevout`/`NegativeFee`/`FeeOutOfRange` errors. It is exactly what `TxFeeOracle` needs internally. |
| `PrevoutSource` + its `HashMap`/`BTreeMap` impls | 154-170 | **Survives.** Becomes the interface between `TxFeeOracle` and whatever answers prevout queries (chain query, in-state resolution, peer bundle). Rename to `PrevoutLookup` only if `prevout` is changed to distinguish "absent" from "unknown" — which it must be, because `Option<TxOut>` conflates `FeeLookup::Unspendable` (permanent) with `ChainBehind` (defer). **This is the one surviving item that needs a signature change.** |
| `IntermediateState` (private) | 284-298 | **Survives, repurposed.** Its layering of in-block outputs over node prevouts is exactly in-state prevout resolution (Iteration 3). Generalise from "outputs created earlier in this block" to "outputs of transactions in `S(X)`". |
| `TransactionFee` + `fee_rate` | 173-190 | **Survives** as the oracle's internal return type. `fee_rate` has no consumer in the new design but is harmless and already tested; keep or drop on taste. Note `fee_rate` divides by `weight.to_wu()` with `checked_div`, so a zero-weight transaction yields `None` rather than panicking — correct. |
| `block_subsidy_sats`, `subsidy_halving_interval`, `INITIAL_SUBSIDY_SATS` | 11-29 | **Survive**, but move out of the fee path: `F_i` never touches the subsidy. They belong with `EdcaConfig::for_network` (`edca/mod.rs:63-78`), which hardcodes `REGTEST_BASE_SUBSIDY_SATS` and would be better computing it. |
| `compute_block_fees` | 241-282 | **Survives for templates only.** Useful for pricing this node's own template when `getTxFees` is unavailable or (per Break 5 item 1) misaligned. Not on the bead path. Keep its `DuplicateSpend` check. |

### Deleted

| item | lines | why |
|---|---|---|
| `verify_fee_commitment` | 46-126 | Route 1. Unsound by construction (§1.1): derives the fee from miner-supplied coinbase value and miner-supplied BIP34 height, and needs a `&Transaction` the bead does not carry. Nothing in the new design accepts a miner-supplied fee at all. |
| `FeeCommitment` | 31-43 | Route 1's return type. Its `height`/`subsidy_sats`/`coinbase_value_sats` fields are all roster-path concerns. |
| `verify_fee_bound` | 320-354 | **The determinism hazard.** Returns a partial sum for an incomplete fee view, and `saturating_add` at `:331` can report `Proven` on overflow. Replaced by `FeeLookup`'s number-free non-`Known` variants. |
| `FeeBound` | 302-316 | Same. `Undecided { computed_fees, missing }` is a payout fork in a type. |
| `BranchKey` + `from_branch` + `to_byte_array` | 357-374 | Keys a template by its merkle branch, i.e. by node-local material (O1). Replaced by `StateKey`, keyed on the DAG-derived set. |
| `root_from_branch`, `hash_pair` | 377-391 | The fold. Deleted from the fee path per Part 1. **Do not simply delete the file's copy**: `template_creator::calculate_merkle_root` (`template_creator.rs:168-180`) is a byte-identical duplicate and is the one that actually built the header at `stratum.rs:1127-1129`. Keep exactly one implementation, in `template_creator`, and keep the existing tests at `template_creator.rs:571,655,684,720`. §2.8's observation that the two agree is correct — both do `sha256d(current ‖ sibling)` with the coinbase always the left child, which is right because leaf 0's subtree is the left child at every level — but a duplicate pair with no cross-test is a latent divergence. |
| `TemplateEntry` + `new` + `from_branch_bytes` + `matches` + `coinbase_value_sats` | 417-481 | Route 3's node-local template record. Its whole premise — that a bead is priced by the template *this node* issued — is what made fee verification node-local. |
| `verify_fee_against_template` | 484-522 | Route 3's check. Superseded by derivation. |
| `TemplateCache` + `new`/`insert`/`get`/`retire_below`/`template_for`/`len`/`is_empty` + its `FeeVerdictSource` impl | 547-620 | Never constructed anywhere (verified). Its `template_for` is a linear scan over retained templates calling `matches` on each (`:584-590`), i.e. O(cache) sha256d folds per bead — gone with the fold. |
| `FeeVerdict` | 525-539 | `Unknown` → `0` at `score.rs:66` is the determinism fork. `Deviated` as a non-rejecting outcome is also wrong in the new model: a deviating claim is now *advisory* and does not change the score, so there is no verdict to represent. Replaced by `FeeIngest`. |
| `FeeVerdictSource` | 541-545 | Only consumer is `VerdictAmplifier`; both go. |
| `ChainAnchor` + `new` | 394-413 | Bundles `prev_blockhash` with a height and subsidy. The new design scopes by `prev_blockhash` alone (`StateKey`'s outer hash); height and subsidy are roster-path. |
| `TxFeeSource` + its three impls | 129-151 | Superseded by `TxFeeOracle`. The `Option<u64>` return is precisely the conflation that `FeeLookup` exists to break: `None` means both "I don't hold it" and "it can't be valid", which must produce opposite verdicts. |

### Outside `validate_fees.rs`

| item | disposition |
|---|---|
| `score.rs:51-69` `VerdictAmplifier` | **Deleted** with `FeeVerdictSource`. Replaced by `DerivedFeeAmplifier`. |
| `score.rs:33-42` `CommittedFeeAmplifier` | **Gated to `#[cfg(test)]` or deleted.** It scores whatever the miner claims; its own doc comment says so. Leaving it `pub` next to the real amplifier is a live mis-wiring risk. |
| `score.rs:17-23` `SubsidyOnlyAmplifier` | **Survives.** It is the honest `F_i ≡ 0` fallback and is exactly option (D) of Iteration 3. |
| `score.rs:9-13` `AmplifierSource` | **Unchanged.** `DerivedFeeAmplifier` fits the existing signature by holding `&Braid` for `compute_bead_hash`. |
| `edca/mod.rs:16-21` `pub use` block | Rewritten: all fourteen re-exported names change. |
| `error.rs:737-838` `FeeProofError` | Shrinks to the variants `transaction_fee` and `compute_block_fees` still raise: `CoinbaseHasNoFee`, `MissingPrevout`, `NegativeFee`, `FeeOutOfRange`, `DuplicateSpend`, `FeeTotalOverflow`. Deleted: `NotCoinbase`, `NoTransactions`, `InvalidMerkleBranch`, `CoinbaseTxidMismatch`, `DuplicateTxid` (moves to `CmempoolError`), `AnchorMismatch`, `MerkleRootMismatch`, `InvalidBip34Height`, `CoinbaseValueOverflow`, `CoinbaseBelowSubsidy`, `FeeCommitmentMismatch`, `FeeExceedsTransactions`. New `CmempoolError` for the delta and state rules. |
| `lib.rs:224-228` template fee summation | **Repurposed**, not deleted: keep the per-transaction `fees` vector instead of folding it away, and feed it to `TemplateFeeOracle`. Change `saturating_add` to `checked_add`, and resolve the `fees[0]` coinbase-slot question (Break 5, item 1) first. |
| `lib.rs:371-382` / `stratum.rs:1272-1283` bead construction | Both must emit the new layout, and the second must stop sending an empty tx list (Break 3). They should share one constructor. |

---

# Part 4 — Re-aim after the auditor's break

The coordinator confirmed the auditor broke §0. **Part 1 of this document reached the same
break independently** (Break 1: two miner-controlled inputs, a public branch, the root
chosen last; Break 2: odd-count duplication does not pin the leaf count; Break 3:
`transaction_ids[0]` is never compared against any real transaction). Iterations 1, 2, 4 and
5 above are unaffected — none of them uses the fold as a proof; Iteration 2 deletes it.
Iteration 3 needs re-aiming, and the auditor's §A.4 adds a vector I under-weighted.

Three corrections I accept, and one I push back on.

**Accepted — the inflation vector is the delta, and it is unbounded.** §A.4 is right and
sharper than my Iteration 3 framing. The attacker's transaction is not a *lie* about a fee;
it is a genuinely valid transaction with a genuinely enormous fee (10 BTC in, 1 sat out).
A *correct* fee oracle returns `Known(1_000_000_000)` and is right to. No amount of oracle
determinism helps, because the number is real. The attacker then prevents the fee ever being
paid by RBF-replacing or double-spending the prevout on the real network, and §2.2's
DAG-derived cmempool keeps the transaction in `S(X)` until the epoch reset (O2). My
Iteration 3 treated `max_delta_fee_sats` as needed *only under option (C)*; that was wrong.
**The cap is needed under every option, including a fully verified oracle.** Iteration 8
makes it structural rather than a bolt-on.

**Accepted — PoW is not checked at ingest, so nothing is pre-committed.** Verified
independently: `Braid::extend` (`braid/mod.rs:90-207`) checks genesis, non-empty parents,
parent presence, and duplicate-bead, and then inserts. There is no target comparison and no
hash-versus-target test anywhere in it. Repo-wide, `is_met_by` appears only at
`stratum.rs:912`, `:1514` and `:4564`, and `validate_pow` only at `:918` — all on this
node's own downstream submissions or a test grinder, never on a peer's bead. Every
"work-bound" statement in the baseline document, and in my Part 1, is therefore conditional
on a check that does not exist. Iteration 6 states it as a prerequisite.

**Accepted — `parent_bead_timestamps` is destroyed on reload.** The auditor's Row 4 finding
that `resolve_parents` (`braid/mod.rs:267-273`) substitutes each parent's own
`start_timestamp`, which is what gets persisted and reloaded, is a stronger version of the
smaller ordering defect I recorded in Break 4. It means the committed vector is not merely
reordered but *replaced*. Consequence for this spec: field 3 of layout (a) must be persisted
verbatim with an explicit position before any signature over `CommittedMetadata` (O7) is
introduced, or every reloaded bead fails verification.

**Push back — parent selection is a weak vector within an epoch, and the auditor says so
too.** §2.2's union is monotone, so `S(X)` grows with the parent set and the fee-maximising
choice is "all tips" — exactly what the honest producer does (`lib.rs:342-361`). A miner
*choosing* parents can therefore only **shrink** its own `S(X)` and lower its own `F_i`.
Within an epoch there is no parent-steering gain to constrain. The two real parent-related
vectors are different:

1. **Cross-epoch replay** (auditor §C2): parents from before a block boundary, so a
   high-fee transaction that has since confirmed is claimed again. Fixed by validating
   `prev_blockhash` against this node's chain and requiring every parent's epoch to equal
   the bead's. Already in Iteration 4's taxonomy; promoted to a named check in Iteration 7.
2. **Introduction timing**, which is the one that actually pays. The attacker does not steer
   *its own* `F_i` upward by picking parents; it makes its own bead the **only** bead on the
   enriched state by being the one that introduces the high-fee transaction. Concurrent
   beads in the same cohort inherit nothing from it (they are not its descendants), so the
   attacker holds `F + f(h)` while its cohort peers hold `F`. Descendants do inherit it, but
   descendants are mostly other miners' beads, so the advantage is confined to the cohort of
   introduction — and that is precisely why it is bounded by `f(h)`, and why capping `f(h)`
   is both necessary and sufficient.

So the restated problem is narrower and more tractable than "constrain parent and delta
selection": **parents need structural validation only (for epoch integrity, not for fee
steering); the delta needs a hard credit bound.** Iterations 7 and 8.

## Iteration 6 — PoW and target validation as a stated prerequisite

**Change.** Before any fee work, at ingest:

```
h = network.block_hash(bead.block_header)          // utils/mod.rs:41-43
1.  Target::from_compact(weak_target) != Target::ZERO
2.  min_target <= weak_target  and  weak_target > bits      (strictly weaker than network)
3.  bits == this node's expected bits for prev_blockhash
4.  Target::from_compact(weak_target).is_met_by(h)           // THE missing check
```

**Resolves.** The auditor's C5. It is a prerequisite for the fee path, not a part of it, but
the fee path is meaningless without it: without (4), producing a bead is free, so every
cost model in this document (orphan-pool bounds, ingest latency, DoS economics) is wrong by
an unbounded factor. Without (2), `block_probability_q` returns `ONE` at `score.rs:97-99`
whenever `weak_target <= bits`, which multiplies any `F_i` by the full probability weight —
so a target lie and a fee lie **compose multiplicatively**, and bounding `F_i` alone
(Iteration 8) does not bound the score.

**Breaks / newly exposes.** Check (3) is epoch-relative: a node that has not reached
`prev_blockhash` cannot know the expected `bits` ⇒ defer, not reject, and
`AddBeadStatus::InvalidBead` is currently the only non-defer outcome `extend` can express,
so the status enum needs a reject-vs-defer distinction it does not have. Check (2) assumes
`weak_target` is an *entitlement* the miner may self-assign; it is not validated against any
pool-issued difficulty, which is outside this scope (auditor's unvalidatable residue) but
means (2) bounds only the *direction*, not the *magnitude*, of a target claim.

**Cost.** One `block_hash` (2 sha256d = ~240 ns) plus three integer comparisons per bead,
and the hash is already computed by `extend` at `braid/mod.rs:122`. **Effectively zero**,
and it is the highest-value check in the entire design: it must run **first**, before any
allocation or I/O, because it is the only thing that makes a bead expensive to produce.

## Iteration 7 — Structural parent and epoch validation

**Change.** Phase A of Iteration 4's gate gains, all pure DAG functions:

```
1.  1 <= parents.len() <= MAX_PARENTS
2.  parent_bead_timestamps.len() == parents.len()
3.  parents are pairwise non-ancestral          (no parent is an ancestor of another)
4.  every parent's epoch == bead.prev_blockhash
5.  bead.prev_blockhash is in this node's chain  (else defer)
```

**Resolves.** The cross-epoch replay of auditor §C2 — check (4) is what makes it impossible
to claim a pre-boundary state's fees after the boundary, and it is the only parent check
the fee path actually needs. (2) closes a length mismatch that is currently not merely
unchecked but *unobservable*, since `resolve_parents` reads only `parents`. (3) is not a fee
concern but removes a free way to inflate the apparent ancestor count, which Iteration 8
makes fee-relevant. (1) bounds the decode allocation and the Iteration-8 ancestor sum.

**Breaks / newly exposes.** (3) requires an ancestor query per parent pair:
`MAX_PARENTS²/2` membership tests. With the persistent ancestor set of Iteration 8 each is
`O(log N)`; with `get_all_ancestors` (`braid/mod.rs:622-661`) it is not viable — that
function builds a `HashMap<usize, HashSet<usize>>` of *every* bead's ancestors, i.e.
`O(N²)` memory (`100k` beads ⇒ ~10^10 entries), and it recomputes an entry it already holds
by clearing it (`:630-634`) and clones the whole map inside the parent loop
(`:648` `let ancestor_ref = ancestors.to_owned();`) — an `O(N²)` clone per parent per bead.
**It must not be called on the ingest path.** This is a verified blocker for any
ancestor-based check and is the single worst performance defect I found.

Honest beads cannot trip (1)-(4): the producer at `lib.rs:342-361` builds both vectors from
one sorted pair list over current tips, and tips are pairwise non-ancestral by definition.

**Cost.** `MAX_PARENTS = 16` ⇒ ≤ 120 ancestor-membership tests at `O(log N)` ≈ 17 steps ⇒
~2,000 pointer hops ⇒ **~10 µs per bead**. Memory: zero beyond Iteration 8's set.

## Iteration 8 — Per-bead capped delta credit: `F_i` as an ancestor-closure sum

This is the iteration that answers the auditor's §A.4 and C4, and it changes `F_i`'s
definition rather than adding a check to it.

**Change.** Replace "`F_i` = sum of fees over the transaction set" with "`F_i` = sum of
**capped per-bead credits** over the ancestor closure":

```
delta_credit(Y) = min( Σ_{t ∈ δ(Y)} fee(t),  MAX_DELTA_CREDIT_SATS )     // fixed at Y's ingest
F_i(X)          = base_credit(epoch)  +  Σ_{Y ∈ anc(X) ∪ {X}} delta_credit(Y)
```

`anc(X)` is the ancestor closure **within the epoch**. `delta_credit(Y)` is computed once,
when `Y` is ingested, and never recomputed — so §2.10's "verify once, score from storage"
is preserved exactly, and the amplifier still reads a stored number.

Why this is the right shape, not just a cap bolted on:

* **It bounds the attacker's marginal gain by its hashrate.** The attacker's contribution to
  any bead's `F_i` is `(number of attacker beads in that bead's ancestor closure) ×
  MAX_DELTA_CREDIT_SATS`. Beads cost work (Iteration 6), so the attacker's share of the
  closure is its hashrate share. There is no longer a per-bead constant the attacker can
  inflate without buying hashrate — which is exactly the property a payout scheme needs,
  and which "sum fees over `S(X)`" does not have at any oracle quality.
* **The cohort-of-introduction advantage is capped.** Per Part 4's push-back, the attacker's
  only real edge is being the sole bead on an enriched state in its own cohort. That edge is
  now `MAX_DELTA_CREDIT_SATS / (B_base + F)`. At `MAX_DELTA_CREDIT_SATS = B_base/1000 =
  312,500 sats` the edge is **+0.1% on `A_i`**, against the **+290,000%** (`A_i` = 6.3e6 ×
  honest, 99.84% of the window's payout) the auditor computes for the uncapped case.
* **It removes the set-wide fee summation from the hot path.** `F_i` needs no per-transaction
  re-summation over 3000 members — just a sum of ≤ 600 per-bead integers.
* **It survives an unconfirmable transaction.** The attacker's 10-BTC-fee transaction earns
  at most `MAX_DELTA_CREDIT_SATS`, the same as a delta of ordinary transactions, so
  manufacturing it buys nothing and the RBF/double-spend half of §A.4 becomes pointless. O2
  stops being load-bearing for *fees* (it remains load-bearing for template mineability).
* **It keeps §2.1's relay incentive.** A miner introducing real transactions still earns
  credit, up to the cap, for its own bead and every descendant. The incentive is weaker than
  uncapped but it was never the attacker-sized number that made it strong.

**Representation.** Store, per bead, one **persistent ordered set of bead indices** = its
ancestor closure, shared structurally with its parents' closures. One insert per bead
(itself) over the parents' union. This single structure serves everything:

```
anc(X)  = union of parents' closures, plus each parent
S(X)    = S_base(epoch)  ∪  ⋃_{Y ∈ anc(X) ∪ {X}} δ(Y)      // for §2.3 and the state key
F_i(X)  = base_credit    +  Σ_{Y ∈ anc(X) ∪ {X}} delta_credit(Y)
```

It also supplies Iteration 7's pairwise non-ancestrality test in `O(log N)`, replacing
`get_all_ancestors` on the ingest path entirely.

**Resolves.** Auditor C4 (a bound independent of set membership — the bound is per bead, and
beads cost work). Auditor §A.4 in full. The coordinator's reframing: the verifier now
computes `F_i` over a quantity *it* bounds, and the miner's only handle is how many beads it
can afford to mine.

**Breaks / newly exposes.**
1. `MAX_DELTA_CREDIT_SATS` is a **new consensus parameter**. All nodes must agree or `F_i`
   diverges. It belongs in `EdcaConfig` (`edca/mod.rs:25-35`) alongside
   `base_subsidy_sats`, and `EdcaConfig` is currently constructed per node from
   `for_network` (`:65-78`) with no agreement mechanism — the same latent divergence O1
   names for the roster, now reaching the fee path. **This is the one node-local value the
   fee path cannot avoid**, and it is a parameter, not data: it diverges only if operators
   are allowed to configure it. It must be a hardcoded constant per network, not a config
   field. Flagged as **D6**.
2. `F_i` is no longer equal to the real template's fee total. It is a *capped proxy*. If the
   EDCA paper's `A_i = B_base + F_i` is meant to be the expected value of the block the
   bead would have produced, the proxy breaks that interpretation and the economics need
   re-deriving. That is an O8-adjacent question I am not resolving. **D7.**
3. Epoch scoping becomes load-bearing for *cost*, not just determinism: the ancestor-closure
   sum is `O(|anc|)` per bead, so it is only viable because `|anc| ≤` beads-per-epoch.
4. Cross-epoch carry-over of credits is now a question §2.4 does not answer:
   `base_credit(epoch)` must summarise the previous epoch's credits for the transactions
   that are still in `S_base`. Deterministic if defined as `Σ delta_credit` over the carried
   beads minus credits for transactions confirmed in the new block — but "minus credits for
   confirmed transactions" needs per-transaction credits, which the per-bead cap has
   deliberately blurred (a capped delta of 5 transactions does not say which transaction got
   how much). **Unresolved: either apportion the cap pro-rata across the delta (deterministic
   but arbitrary) or define `base_credit` as a flat function of the carried set's size.**
   Recorded as **D5a**.

**Cost.** Per bead: parents' closure union (`O(|smaller closure| · log)` worst case, near-free
when parents are on near-identical closures) + 1 insert + a sum over `|anc| ≤ 600` u64s ⇒
~600 pointer hops + 600 adds ⇒ **~5 µs**. Fee oracle calls: `|δ| ≤ 5` per bead, unchanged.
Memory: `log2(600) ≈ 10` new tree nodes per bead × ~48 B = **~500 B per bead**, 600 beads
per epoch ⇒ **~300 kB resident** — six times better than Iteration 5's txid-set figure,
because the set now holds bead indices (one insert per bead) rather than txids (five). IBD:
the per-bead sum makes it `O(beads_per_epoch²)` per epoch = `600² = 360k` additions per
epoch, `144` epochs/day ⇒ 52 M additions/day ⇒ **under a second of CPU per simulated day**.
The set-wide `state_key` digest (~180 µs/bead, Iteration 2) now dominates the fee path's IBD
cost at ~18 s per 100k beads.

## Delta to the Converged Specification

Iterations 6-8 change Part 3 as follows. Everything else in Part 3 stands.

**(a) layout.** Unchanged, with one addition: field 11 `additional_tx_ids` acquires the
decode-time constraint `len <= MAX_DELTA` *and* the ingest-time constraint
`delta_credit <= MAX_DELTA_CREDIT_SATS`. Field 13 `fee_total_sats` stays advisory. No new
wire field is needed for the cap — it is a protocol constant, deliberately not carried
(carrying it would let a miner propose its own bound).

**(b) signatures.** Three changes:

```rust
/// Protocol limits on a bead's delta. Consensus constants, NOT operator
/// configuration: two nodes with different values derive different `F_i`,
/// which is a payout fork. They must be hardcoded per network, in the same
/// place `REGTEST_BASE_SUBSIDY_SATS` lives (`edca/mod.rs:61`), and must not
/// become fields of a user-supplied `EdcaConfig`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DeltaLimits {
    /// Maximum `|delta(X)|`. 5, per §2.1.
    pub max_delta_len: usize,
    /// Maximum fee credit one bead's delta may contribute to `F_i`, in
    /// satoshis, regardless of what its transactions actually pay.
    ///
    /// This is the bound that makes `F_i` safe. Without it a single valid
    /// transaction paying 10 BTC to fee — which a correct fee oracle prices
    /// correctly, because the fee is real — lifts one bead's `A_i` to 3.9x
    /// honest, and `MAX_MONEY` lifts it to 6.3e6x. Capped, a miner's
    /// marginal gain is proportional to the beads it can mine, i.e. to its
    /// hashrate, which is the property a payout scheme needs.
    ///
    /// Suggested: `B_base / 1000` (312,500 sats on mainnet), giving a
    /// worst-case single-bead advantage of +0.1% on `A_i`.
    pub max_delta_credit_sats: u64,
}

/// A bead's own contribution to its descendants' `F_i`, in satoshis.
///
/// `min(sum of delta fees, max_delta_credit_sats)`. Computed once at the
/// bead's ingest and never recomputed, so §2.10's "verify once, score from
/// storage" holds and the amplifier never re-derives.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct DeltaCredit(pub u64);

/// A bead's epoch-local ancestor closure, with structural sharing.
///
/// One insert per bead over the union of its parents' closures, so a child
/// shares every untouched subtree with its parents: ~500 B of new nodes per
/// bead, ~300 kB for a 600-bead epoch.
///
/// This single structure serves the whole fee path:
/// `F_i` is the sum of `delta_credit` over it, `S(X)` is `S_base` unioned
/// with the deltas of its members, and Iteration 7's pairwise
/// non-ancestrality test is `O(log N)` membership on it.
///
/// It exists specifically so that `Braid::get_all_ancestors`
/// (`braid/mod.rs:622-661`) is never called on the ingest path. That
/// function materialises every bead's ancestor set in one
/// `HashMap<usize, HashSet<usize>>` — `O(N^2)` memory — and clones the whole
/// map once per parent per bead (`:648`). It is not usable at ingest.
pub type AncestorClosure = /* persistent ordered set of bead indices */;
```

and `CmempoolState` gains the two derived quantities, with `fee_total_sats` redefined:

```rust
pub struct CmempoolState {
    pub epoch: BlockHash,
    /// This bead's epoch-local ancestor closure, including itself.
    pub closure: AncestorClosure,
    /// This bead's own capped credit.
    pub delta_credit: DeltaCredit,
    /// `S(X)`, for the §2.3 disjointness rule and the state key.
    pub members: PersistentTxidSet,
    pub key: StateKey,
    /// `F_i` = `base_credit(epoch)` + the sum of `delta_credit` over
    /// `closure`. A **capped proxy** for the template's fee total, not the
    /// total itself — see D7.
    pub fee_total_sats: u64,
}
```

**(c) worked example.** The numbers change, and the change is the point. With
`MAX_DELTA_CREDIT_SATS = 312,500` all six beads' deltas are under the cap, so every `F_i`
and `A_i` in Part 3(c) is unchanged — the cap is invisible to honest traffic. Now add a
seventh bead:

* `H`: parents `{C}`, `δ(H) = {t7}` where `t7` pays **1,000,000,000 sats** (10 BTC in,
  1 sat out, a genuinely valid transaction).

| | uncapped (Part 3 rules) | capped (Iteration 8) |
|---|---|---|
| `delta_credit(H)` | 1,000,000,000 | `min(1e9, 312,500)` = **312,500** |
| `F_H` | 4,500 + 1e9 = 1,000,004,500 | 4,500 + 312,500 = **317,000** |
| `A_H` | 1,312,504,500 | **312,817,000** |
| `A_H / A_D` (same cohort as `D`, `A_D` = 312,505,400) | **4.20×** | **1.001×** |

The uncapped row is the auditor's §A.4 attack at this document's own example scale: one bead
takes 4.2× a cohort peer's weight, repeatable every bead, for a transaction the attacker
then double-spends so the fee is never paid. The capped row bounds it at +0.1%.

**(d) migration.** Two additions. `block_subsidy_sats` / `subsidy_halving_interval`
(`validate_fees.rs:15-29`), which I had marked "survives, moves out of the fee path", should
instead become the source of `MAX_DELTA_CREDIT_SATS`'s derivation (`B_base/1000`), so the
cap halves with the subsidy and the +0.1% bound is epoch-invariant. And `FeeLookup::Known`
must be understood as *correct but not safe*: a capping step sits between the oracle and
`F_i`, so no oracle hardening can be traded against the cap.

---

# Part 5 — Unresolved Decisions

Each needs a maintainer decision. I state what I would choose and why, but none of these can
be settled by reading the code.

### D1 — The free-rider: is `A_i` allowed to reward a miner who held no transactions?

Once `F_i` is derived, nothing requires a miner to hold, validate or relay any transaction
to be credited the canonical set's fees. A bead with an empty local mempool collects the
same `F_i` as one that assembled the whole template. The fee path cannot detect this — `F_i`
is correct by construction — and detecting it requires binding the bead to a *constructible*
coinbase, i.e. the roster path and O1. **§0's "O1 is irrelevant to the fee path" is true for
`F_i` determinism and false for `A_i`'s economic meaning.** Worse, such a bead is an
unmineable block, so if it meets the network target the pool loses the entire reward, not
just the fees.

*My view*: accept it for now and record it, because Iteration 8's cap means the free-rider
gains nothing *relative* to an honest miner (both get the same inherited credits; neither
can inflate). The unmineable-block risk is real but it is a mineability problem, and
mineability is the roster path's job.

### D2 — Does braidpool acquire a prevout/UTXO interface to bitcoind?

`node/schema/mining.capnp` exposes no UTXO lookup, no raw-transaction fetch and no mempool
query, so a transaction obtained from a peer **cannot be priced at all** today. Options are
Iteration 3's (A) add a chain interface, (B) peers serve prevout bundles (asserted, not
verified), (C) the introducing bead commits the fee (needs the cap, which Iteration 8 now
supplies anyway), (D) `F_i ≡ 0` via the existing `SubsidyOnlyAmplifier`.

*My view*: (A). It is the only option under which `fee(t)` is *verified*, and its cost is
small (≈0.6 ms/bead steady state, ≈375 ms per cold epoch). But note that **Iteration 8's cap
substantially reduces what (A) buys**: with the credit capped per bead, the damage from a
mispriced transaction is bounded at `MAX_DELTA_CREDIT_SATS` regardless of oracle quality. So
(C) + the cap is a defensible interim that needs nothing from bitcoind, and (D) is a
defensible interim that needs nothing at all. This is the single biggest scope decision in
the design.

### D3 — The double-spend tiebreak (O3)

Two beads in the same cohort whose deltas spend the same outpoint. The rule must be pinned
or `S(X)` is not unique and honest beads diverge. Candidates: lowest txid wins; lowest bead
hash wins; the bead in the earlier cohort wins with a hash tiebreak within a cohort.

*My view*: lowest bead hash of the *introducing bead* — it is already computed
(`braid/mod.rs:122`), it is PoW-weighted once Iteration 6 lands so it cannot be ground
cheaply, and it does not depend on cohort assignment, which is itself recomputed as the DAG
grows (`braid/mod.rs:141-199` truncates and rebuilds cohorts on every insert, so any rule
keyed on cohort ordinal is unstable).

### D4 — What happens when `state_key` persistently disagrees?

Iteration 4 defers while any ancestor is unsettled, then accepts with the derived `F_i` and
raises a counter. It never rejects, because rejection must be a pure DAG decision and
"persistently" is a timing word. But a bead that permanently claims a state no node will
ever derive then stays in the DAG forever, scored on a state it did not mine.

*My view*: accept and score on the derived value. The alternative — reject after a timeout —
makes rejection node-local and forks the DAG, which the brief names as strictly worse than a
dropped bead. But this means `state_key` is *only* a defer hint and never a verdict, so it
should be documented as such rather than looking like a validation field.

### D5 — The epoch base set, `S_base(epoch)`

§2.4's "reset at each new Bitcoin block" taken literally gives near-empty templates for a
full block interval at every epoch start (a 3000-transaction set refilling at ≤ 5
transactions per bead needs ~600 beads). Iteration 4 proposes
`S_base(E_new) = (⋃_{X ∈ A} S(X)) \ txs(B_new)` with `A` the previous epoch's beads that are
ancestors of the first bead of `E_new` — both operands consensus objects, so deterministic,
but per-bead rather than global and therefore more work.

**D5a**, which I could not resolve: `base_credit(epoch)` must carry forward the credits
belonging to the transactions that survive into `S_base`, but Iteration 8's per-bead cap
deliberately does not record which transaction in a delta got how much of the capped credit.
Either apportion the cap pro-rata across a delta (deterministic but arbitrary, and it
reintroduces per-transaction fee bookkeeping the cap was meant to remove) or define
`base_credit` as a flat function of `|S_base|`. I lean to the latter — it is simpler and the
credit is already a proxy, not a measurement (D7) — but it is a design choice with economic
consequences I have not worked through.

### D6 — Where `MAX_DELTA_CREDIT_SATS` and `DeltaLimits` live

They are consensus constants: two nodes with different values derive different `F_i`. But
their natural home, `EdcaConfig` (`edca/mod.rs:25-35`), is constructed per node by
`for_network` (`:65-78`) with no agreement mechanism, and `retention_num`/`retention_den`/
`dust_limit_sats` already sit there as apparently operator-tunable fields. **`F_i` acquires
its only unavoidable node-local dependence here, and it is a parameter rather than data.**

*My view*: hardcode them per `PoolNetwork` as constants beside `REGTEST_BASE_SUBSIDY_SATS`
(`edca/mod.rs:61`) and do **not** add them to `EdcaConfig`. Separately, the existing
`EdcaConfig` fields that affect scoring should be audited for the same hazard — that is
O8's territory, not mine, but the hazard is identical.

### D7 — Is a capped `F_i` still the quantity EDCA's `A_i` is supposed to be?

Iteration 8 makes `F_i` a **capped proxy** for the template's fee total, not the total. If
`A_i = B_base + F_i` is meant to be the expected value of the block the bead would have
produced, the cap breaks that reading: a bead on a genuinely fee-rich template is credited
less than it would really have earned. The alternative is an uncapped `F_i`, which the
auditor shows is a 6.3e6× inflation vector. There may be no formulation that is both
faithful to the paper and safe.

*My view*: safety wins; the paper's economics need re-deriving against a capped amplifier.
This is adjacent to O8 and I am not resolving it. Worth raising with whoever owns the EDCA
derivation, because it may change what `B_base` should be.

### Prerequisites this specification depends on and does not itself provide

1. **PoW checked at ingest** (Iteration 6). Without it every cost and DoS figure in this
   document is wrong by an unbounded factor, because beads are free to produce.
2. **`AddBeadStatus` must distinguish permanent reject from defer.** It currently has
   `InvalidBead` and `ParentsNotYetReceived`; the taxonomy in Iteration 4 needs a third
   outcome and a reason payload, or the gate's verdicts cannot be expressed.
3. **The orphan pool must be bounded.** `orphan_beads: Vec<Bead>` (`braid/mod.rs:36`) is
   unbounded with a linear retry scan and recursion per promotion
   (`braid/mod.rs:209-254`, recursive call at `:238`). Iteration 4 doubles the reasons a
   bead parks there.
4. **Decode must be hardened before any of this ships.** `TxIdVec::consensus_decode`
   (`committed_metadata/mod.rs:51-53`) and `TimeVec::consensus_decode` (`:27-29`) call
   `Vec::with_capacity` on an unbounded `u64`, reachable from `BeadCodec::read_request`
   (`bead/mod.rs:140-148`); and `TimeVec`'s decode `.unwrap()`s
   `Time::from_consensus` (`:34`), which errors below 500,000,000 — a panic from a crafted
   gossip message.
5. **`get_all_ancestors` must not be on the ingest path** (`braid/mod.rs:622-661`:
   `O(N²)` memory, plus a whole-map clone per parent per bead at `:648`).
6. **`parent_bead_timestamps` must be persisted verbatim** before any signature over
   `CommittedMetadata` (O7), since reload currently replaces it with the parents' own
   `start_timestamp` values (`braid/mod.rs:267-273`, `db_handlers.rs:534-544`).
7. **The `getTxFees` coinbase-slot question must be settled** (Part 1, Break 5 item 1):
   whether `fees[0]` is the coinbase's `-nFees` determines both the index alignment and
   whether `lib.rs:224-228` currently pins `fee_total_sats` at `u64::MAX`. *Unverified*
   against Core's source, which this repo does not vendor.
