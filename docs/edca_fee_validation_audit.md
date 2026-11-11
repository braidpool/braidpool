# EDCA Fee Validation — Adversarial Audit

**Branch**: `edca_payout_implementation` @ `bf110ae`
**Scope**: fee validation only — every miner-supplied input that affects `fee_total_sats`
or its re-verification, since that value feeds `A_i = B_base + F_i`.
**Method**: every claim below is anchored to `file:line` in this tree. Inferences are
marked **unverified**.

---

## 0. Ground facts established before the matrix

These are the load-bearing facts. Everything in §A–§D rests on them.

| # | Fact | Evidence |
|---|---|---|
| G1 | The bead hash covers **the 80-byte header and nothing else**. `committed_metadata` is not in the preimage. | `node/src/utils/mod.rs:41-43` → `network.block_hash(header)` → `node/src/config.rs:167-172` → `header.block_hash()` / `Cpunet::block_hash(header)`. `impl_consensus_encoding!(Bead, …)` at `node/src/bead/mod.rs:48` is wire encoding only, never hashed. |
| G2 | **`Braid::extend` performs no proof-of-work check at all.** It checks: non-empty parents, all parents present, not already in DAG. Nothing else. | `node/src/braid/mod.rs:90-207`. No `Target`, `is_met_by`, `bits` or hash comparison anywhere in the function. |
| G3 | `is_met_by` exists only on the node's **own downstream submissions**, never on a peer's bead. | `node/src/stratum.rs:912`, `:1142`, `:1514`, `:4564`. Zero occurrences in `braid/`, `edca/`, `main.rs` gossip path. |
| G4 | The gossip ingest path decodes a bead and calls `extend` **immediately**, with no validation between. | `node/src/main.rs:1143` (`deserialize`) → `:1151` (`braid_data.extend(&bead)`). Same for IBD responses: `node/src/main.rs:1595`. Same for RPC-injected beads: `node/src/rpc_server.rs:338`. |
| G5 | Every entry point in `validate_fees.rs` has **zero callers**; `EdcaState::from_braid` has **zero production callers**. | `grep` for `from_braid`, `verify_fee_commitment`, `verify_fee_bound`, `TemplateCache::new`, `TemplateEntry::new`, `VerdictAmplifier` outside `edca/` and `tests` returns only the `pub use` re-export at `node/src/edca/mod.rs:13`. |
| G6 | `root_from_branch` and `calculate_merkle_root` are **byte-for-byte identical**: both `sha256d(current ‖ sibling)` with the coinbase always the left child, no length prefix, no domain separation. | `node/src/edca/validate_fees.rs:377-391` vs `node/src/template_creator.rs:168-180`. The producer side that built the header uses the latter at `node/src/stratum.rs:1128-1130`. Duplicate implementations, no cross-test. |
| G7 | `bitcoin::merkle_tree::calculate_root` **returns the single leaf unchanged** for a 1-element list and **duplicates the last element** on odd counts. | `bitcoin-0.32.8/src/merkle_tree/mod.rs:65-69` and `:80`. |
| G8 | `fee_total_sats` is range-checked against `MAX_MONEY` **only in `Decodable`**. Locally produced beads and DB-loaded beads bypass it. | Check at `node/src/committed_metadata/mod.rs:147-153`. Bypassed at `node/src/lib.rs:381` (local construction) and `node/src/db/db_handlers.rs:625-629` (`u64::try_from(i64)` admits up to `i64::MAX` ≈ 9.2e18 ≫ `MAX_MONEY` 2.1e15). |
| G9 | `TxIdVec`/`TimeVec` decode a **u64 length** and call `Vec::with_capacity(len as usize)` before reading any element. | `node/src/committed_metadata/mod.rs:30-31` and `:54-55`. |
| G10 | `TimeVec::consensus_decode` calls **`.unwrap()`** on `Time::from_consensus`, which errors for any value `< 500_000_000`. | `node/src/committed_metadata/mod.rs:34`; `bitcoin-units-0.1.3/src/locktime/absolute.rs:159-165` (`is_block_time`). Remote panic. |
| G11 | `transaction_ids` has **no ordering column** in persistence and is reloaded by an unordered `SELECT`. | Schema `node/src/db/schema.sql:31-35` (`UNIQUE(bead_id, txid)`, no sequence). Reload `node/src/db/db_handlers.rs:483-515` — `SELECT bead_id, txid FROM Transactions WHERE bead_id IN (…)` with **no `ORDER BY`**, pushed in result order. |
| G12 | `UNIQUE (bead_id, txid)` means a bead carrying a duplicate txid **cannot be persisted**; the bulk insert runs inside one transaction over a chunk of up to 500 beads. | `node/src/db/schema.sql:34`; `BATCH_INSERT_THRESHOLD = 500` at `node/src/db/db_handlers.rs:19`; chunk insert at `:179-260`. |
| G13 | `extra_nonce_1`/`extra_nonce_2` are **`u64`**, losing the byte-length that Stratum negotiated per connection. | `node/src/uncommitted_metadata/mod.rs:14-15`; produced by `u64::from_str_radix` at `node/src/stratum.rs:978` and `:989` from a `Vec<u8>` extranonce1 (`:224`) whose size is 8 in direct mode (`node/src/lib.rs:118,124`) but **4** upstream (`node/src/stratum.rs:40`, `UPSTREAM_EXTRANONCE1_SIZE`) and variable in proxy mode (`:3529` `.unwrap_or(8)`). |
| G14 | `block_probability_q` returns `ONE` (probability 1) whenever the committed `weak_target` is **harder than or equal to** the header's `bits`, and neither value is validated against anything. | `node/src/edca/score.rs:91-105`, specifically `:97-99`. |

**The pre-committed / correct distinction.** G1 + G2 together mean that at ingest
today nothing is even *pre-committed*: with no PoW check, the header's merkle root is
not "bound to work", it is simply another attacker-chosen 32-byte field. Every claim
below of the form "bound by the merkle root" is therefore **conditional on a PoW check
being added at ingest**. Where that matters I say so explicitly.

---

## 1. Validation matrix

Baseline for every quantitative claim: `B_base = DEFAULT_BASE_SUBSIDY_SATS = 312_500_000`
sats (`node/src/edca/mod.rs:47`), honest `F_i ≈ 2e7` sats at current mainnet fee levels
(**unverified**, order-of-magnitude), so honest `A_i ≈ 3.325e8`. `MAX_MONEY = 2.1e15`.
Honest probability factor at weak-share difficulty ~1e6× easier than network ≈ `1e-6`,
so honest `S_i ≈ 332` q-sats. Payout share is `U_m / U_total`
(`node/src/edca/state.rs:206-236`), linear in `S_i`, so a factor-`k` inflation of `A_i`
is a factor-`k` inflation of that bead's claim on the coinbase.

---

### Row 1 — `committed_metadata.fee_total_sats`

- **Field**: `node/src/committed_metadata/mod.rs:82`. Produced at `node/src/lib.rs:381` from
  `submitted_job.blocktemplate.fee_total_sats` (`node/src/stratum.rs:1007`), which is the
  node's own `saturating_add` fold over bitcoind's `components.fees` (`node/src/lib.rs:228-234`).
- **Reaches**: `CommittedFeeAmplifier::fee_sats` → `node/src/edca/score.rs:36-41`
  → `EdcaState::from_braid` `:107` → `fee_amplifier` `:109` → `raw_score` `:111` →
  per-miner `scores` `:113-120`. Also `verify_fee_commitment:112`, `verify_fee_against_template:504`,
  `TemplateCache::verdict:611`.
- **Current binding**: **nothing.** Not in the hash preimage (G1). Not in the merkle root —
  only `transaction_ids` is. The `comm_pub_key`/`signature` pair that could authenticate it
  is never verified anywhere in the tree (`node/src/uncommitted_metadata/mod.rs:17` is decoded
  at `:59` and read nowhere else). The only constraint is the `Decodable` range check
  `≤ MAX_MONEY` at `node/src/committed_metadata/mod.rs:147-153`, and that check is bypassed
  on two paths (G8): local construction (`node/src/lib.rs:381`) and DB reload
  (`node/src/db/db_handlers.rs:625-629`, which admits up to `i64::MAX`).
- **Attack**: set `fee_total_sats = MAX_MONEY = 2.1e15`. `A_i = 3.125e8 + 2.1e15 ≈ 2.1e15`,
  i.e. **6.3e6×** an honest bead. Against a window holding 10,000 honest beads
  (`U_honest = 10^4 × 3.325e8 = 3.325e12` undecayed), the single bead's share is
  `2.1e15 / 2.1033e15 = 99.84%` of the entire pool payout for the whole retention window.
  Via the DB-reload path the ceiling rises to `i64::MAX ≈ 9.2e18`, at which point
  `fee_amplifier`'s `checked_add` (`node/src/edca/score.rs:73`) still succeeds but a second
  such bead makes `raw_score`'s `(A as u128) << 64` reach 1.7e38 and the per-miner
  `checked_add` at `state.rs:116` eventually returns `EdcaError::WeightOverflow`, which
  `from_braid` propagates with `?` — **one bead aborts the entire payout computation for
  every miner** (availability, not theft). `CommittedFeeAmplifier` clamps with
  `.min(MAX_MONEY)` at `score.rs:40`, so this second effect needs an amplifier that reads the
  stored value unclamped — which is exactly what design §2.10 proposes.
- **Detectable?** From a bead alone: **No** — the value is a bare integer with no witness.
  With DAG-derived state: **Only-if** `S(X)` is uniquely derivable *and* the node can price
  every tx in it, i.e. only-if O2/O3/O4 are pinned. With the node's own bitcoind: **Yes** for
  the subset of `S(X)` whose transactions and prevouts the node holds — a tx fee is objective
  (`inputs − outputs`, `node/src/edca/validate_fees.rs:193-238`) so any node holding tx +
  prevouts computes the same number.
- **Check**: do not read `fee_total_sats` for scoring at all. Compute
  `F_i := Σ fee(tx) for tx ∈ S(X)` locally and use that; treat the committed field as a
  *claim to be compared*, rejecting only on `claim > computed` when the computed set is
  complete. `verify_fee_bound` (`:320-354`) is the right shape but has two defects: the
  `saturating_add` at `:331` can report `Proven` on saturation (sum `≥ claim` because it
  pinned at `u64::MAX`), and it is reached only via a `FeeCommitment` that route 1 built from
  miner data. Belongs at ingest, after the structural checks, before the DAG insert.
- **Failure response**: `claim > computed` with a complete set → **reject** (no honest bead
  can produce it: the honest producer copies the node's own template total,
  `node/src/stratum.rs:1007`). Incomplete set → **defer to orphan pool** (an honest bead can
  trivially trigger this — the verifier may simply not hold the txs yet). Never
  accept-and-log: the field is the payout multiplier.

---

### Row 2 — `committed_metadata.transaction_ids[0]` (the claimed coinbase txid)

**This is the row that decides the §0 hypothesis.**

- **Field**: `node/src/committed_metadata/mod.rs:67`, element 0. Produced at
  `node/src/lib.rs:331-335` as `compute_txid()` of `candidate_block.txdata[0]`.
- **Reaches**: `TemplateCache::verdict` → `node/src/edca/validate_fees.rs:606` → `template_for`
  `:584-590` → `TemplateEntry::matches` `:471-473` → `root_from_branch` `:385-391`. Also
  `verify_fee_commitment:56-66` and `verify_fee_against_template:496`.
- **Current binding**: **nothing.** Nothing in the tree ever recomputes a coinbase txid from a
  transaction and compares it (`verify_fee_commitment` does so at `:60-66`, but only against a
  `&Transaction` the caller supplies, and the bead carries no transactions —
  `node/src/bead/mod.rs:43-47`). The field is 32 arbitrary bytes.
- **Attack**: the fold is a **forward computation with two miner-controlled inputs**.
  `derived_branch` is public (any node that can derive `S(X)` can derive it), so the miner:
  1. picks any parent set `P` and derives `S(X) = ∪S(P) ∪ delta` themselves,
  2. computes `branch := branch(S(X))`,
  3. picks `cb := any 32 bytes`,
  4. sets `header.merkle_root := fold(cb, branch)`,
  5. mines that header.
  `fold(claimed_coinbase_txid, derived_branch) == header.merkle_root` then holds **by
  construction**. The miner needs no coinbase, no transactions, no bitcoind, no mempool. The
  degenerate case is even cheaper: with `transaction_ids = [cb]` and an empty branch,
  `root_from_branch(cb, [])` returns `cb` unchanged (`:386-390`) and
  `bitcoin::merkle_tree::calculate_root` returns the single leaf unchanged (G7), so setting
  `merkle_root := cb` satisfies both route 1's root check (`:74-85`) and the fold.
  Effect on `F_i`: the miner is credited `F(S(X))` for a set they never held and cannot
  produce. Effect on the pool: full fee credit with **zero** block-producing capability —
  the share is unmineable, because no transaction hashes to `cb`.
- **Detectable?** From a bead alone: **No.** The bead carries no coinbase and no witness that
  `cb` is a txid of anything. With DAG-derived state: **No** — `S(X)` says nothing about the
  coinbase. With the node's own bitcoind: **No** — the coinbase of an unbroadcast weak share
  is not in anyone's mempool. **Only-if** the verifier reconstructs the expected coinbase
  itself (design §2.8) and compares, which requires the coinbase prefix/suffix to be
  DAG-derivable (O1) and the extranonce window length to be protocol-fixed or carried in the
  bead (see Row 11).
- **Check**: `expected_txid := txid(derived_prefix ‖ en1 ‖ en2 ‖ derived_suffix)`, then
  `fold(expected_txid, derived_branch) == header.merkle_root`. Only this makes the left leaf a
  value the node independently holds, which is the design's own rule §1.2. Belongs at ingest,
  after the structural checks. Secondary, cheap, and available today: reject
  `transaction_ids.len() == 1` combined with `merkle_root == transaction_ids[0]` as the
  degenerate fold, and reject any duplicate txid (route 1 already does this at `:69-72`; the
  fold route has no such check).
- **Failure response**: **score-at-zero and quarantine, not reject**, until O1 is resolved —
  because an honest bead from another node's job will also fail a reconstruction the verifier
  cannot perform (that is O1 exactly), so rejecting forks the DAG. Once the coinbase is
  DAG-derivable, **reject**: no honest bead can fail it.

---

### Row 3 — `committed_metadata.transaction_ids[1..]` (the tx set; proposed `cmempool_tx_ids` / `additional_tx_ids`)

- **Field**: `node/src/committed_metadata/mod.rs:67`; `TxIdVec` decode at `:52-61`.
- **Reaches**: `verify_fee_commitment:74-85` (root recomputation), `verify_fee_bound:329`
  (fee summation, skipping index 0). Under the design it also reaches the cmempool delta rule
  §2.3 and hence every descendant's `S(X)`.
- **Current binding**: the merkle root, **and only in route 1** — `calculate_root` over the
  full list vs `header.merkle_root` (`:74-85`). The fold route (route 3, and the hypothesis)
  never touches `transaction_ids[1..]`: `verdict` reads only element 0 (`:606`). So under the
  hypothesis the committed list beyond the coinbase is **not consumed at all** — the set used
  for `F_i` is the verifier's `S(X)`, not the bead's list. Decode applies no bound on length:
  `Vec::with_capacity(u64)` at `:55` (G9).
- **Attack**: three distinct ones.
  (a) **Leaf-count ambiguity (CVE-2012-2459 shape).** `calculate_root` duplicates the last
  element on odd counts (G7), so leaves `[cb,t1,t2]` and `[cb,t1,t2,t2]` give the same root
  and the *same* coinbase branch `[t1, H(t2‖t2)]`. The fold therefore does not pin the leaf
  count, only the branch length the *verifier* chose. Fee impact under the hypothesis: none
  directly, because `F_i` comes from the verifier's `S(X)` — but it means the fold cannot be
  cited as proof that "the non-coinbase leaves are exactly `S(X)`"; it proves only
  "consistent with `S(X)` up to last-element duplication".
  (b) **Set substitution is free** because of Row 2: the miner claims whichever `S(X)` pays
  best and makes the fold pass with a fake `cb`.
  (c) **Unbounded list.** `transaction_ids` with a declared length of `u64::MAX` triggers
  `Vec::with_capacity` of 32 × 2^64 bytes → capacity-overflow abort before a single byte is
  read. One ~30-byte gossip message kills the node (see §D).
- **Detectable?** (a) **Yes**, trivially: reject any duplicate txid and require
  `transaction_ids.len()` to equal `1 + |S(X)|`. (b) **No** from a bead alone. (c) **Yes**,
  at decode.
- **Check**: at decode, bound the declared length (a block holds ~4e6/60 ≈ 6.7e4 txs; a bound
  of 2^17 is generous and cannot reject an honest bead) and read incrementally rather than
  pre-allocating. At ingest: duplicate-txid rejection, `len == 1 + |S(X)|`, and
  `transaction_ids[1..] == canonical_order(S(X))` element-by-element — which makes the fold
  redundant for set-proving and leaves it doing only what it can do (binding the claim to the
  work).
- **Failure response**: decode-bound violation → **reject and penalise the peer**
  (`peer_manager.penalize_for_invalid_bead` already exists, `node/src/main.rs:1602`).
  Duplicate txid → **reject** (an honest block never repeats a txid; the producer path
  `node/src/lib.rs:331-335` maps over real txdata so cannot). Set mismatch → **defer**, since
  an honest bead on a state this node has not built yet legitimately mismatches (O2/O3/O4).

---

### Row 4 — `committed_metadata.parents`

- **Field**: `node/src/committed_metadata/mod.rs:68`. Produced at `node/src/lib.rs:342-361`
  as *all current tips*, hash-sorted.
- **Reaches**: `Braid::extend` `node/src/braid/mod.rs:106-120` (presence), `:143-172`
  (cohort recomputation), `resolve_parents` `:255-276`, `get_all_ancestors` `:622-660`. Under
  design §2.2 the parent set **determines `S(X)`** and therefore `F_i` entirely.
- **Current binding**: existence in `bead_index_mapping` only (`:111`). No check that the
  parents are tips, that they are not ancestors of each other, that `parents.len()` matches
  `parent_bead_timestamps.0.len()`, or that the parents share the bead's `prev_blockhash`
  epoch. Not covered by the merkle root. Not in the hash preimage (G1).
- **Attack**: `parents` is the miner's handle on `S(X)`, hence on `F_i`, at zero cost. The
  miner enumerates reachable parent sets, derives `S(P)` for each, and commits the one with the
  largest fee total. Because §2.2's union is monotone, the maximiser is "all tips" — which is
  what honest nodes do, so the honest-vs-adversary differential from parent choice alone is
  small. The real leverage is **cross-epoch parent selection**: choose parents from before a
  Bitcoin block boundary, when a very high-fee transaction was still in the cmempool and had
  not yet confirmed, and claim its fee again. Under §2.4 the state is scoped to
  `prev_blockhash`, so this requires `prev_blockhash` to be stale too — see §C2. Second,
  the committed `parent_bead_timestamps` vector is **never persisted and never read**:
  `resolve_parents` (`node/src/braid/mod.rs:267-273`) substitutes each *parent's own*
  `start_timestamp`, and that substitute is what the DB writer stores
  (`node/src/db/db_handlers.rs:158-165`) and what reload puts back into
  `parent_bead_timestamps` (`node/src/db/db_handlers.rs:534-544`). So a bead's witnessed
  timestamps are silently replaced by other data on the first restart, and
  `parents.len() != parent_bead_timestamps.0.len()` is not merely unchecked, it is
  unobservable downstream. Any future check or signature over `committed_metadata` will fail
  for every reloaded bead.
- **Detectable?** **Yes** for the structural properties (parents are tips / not mutually
  ancestral / lengths equal / same epoch) — all from the DAG the verifier already holds.
  **No** for "did the miner pick these parents to maximise fees", and that is not a detectable
  property because an honest miner also picks the fee-maximising parent set. This is a
  protocol-design consequence, not a validation gap.
- **Check**: `parents.len() == parent_bead_timestamps.0.len()`, `1 ≤ parents.len() ≤ K`, no
  parent is an ancestor of another parent, every parent's `prev_blockhash` equals the bead's
  (or is its immediate predecessor across a boundary). All at ingest, all cheap, all
  DAG-local. Additionally bound `parents.len()` at decode.
- **Failure response**: length mismatch and mutual-ancestry → **reject** (the honest producer
  at `node/src/lib.rs:342-361` builds both vectors from the same sorted pair list and uses
  tips only, so cannot trigger either). Epoch mismatch → **defer** across a genuine block
  race, **reject** when the claimed epoch is not in the node's chain at all.

---

### Row 5 — `committed_metadata.parent_bead_timestamps`

- **Field**: `node/src/committed_metadata/mod.rs:69`, `TimeVec` decode at `:28-39`.
- **Reaches**: no fee-path consumer today. Included because it is the single worst input in
  the bead and it is length-coupled to `parents`, which the fee path does depend on.
- **Current binding**: none. Decode calls **`.unwrap()`** on `Time::from_consensus`
  (`:34`), which errors for any value `< 500_000_000` (G10).
- **Attack**: a gossip bead with one `parent_bead_timestamps` entry of `0` **panics the
  decoding task**. The decode happens at `node/src/main.rs:1143` inside the swarm event loop;
  a panic there takes down the node's networking (or the process, depending on panic policy —
  **unverified** which). Cost to the attacker: one ~200-byte floodsub message, no PoW. Also
  `Vec::with_capacity(u64)` at `:31` gives the same allocation abort as Row 3(c).
- **Detectable?** **Yes**, at decode, for free — the error is already available, it is being
  discarded by `.unwrap()`.
- **Check**: replace `.unwrap()` with the `map_err` pattern already used four lines below for
  `start_timestamp` (`:130-135`). Bound the declared length.
- **Failure response**: **reject** at decode. An honest producer cannot trigger it: timestamps
  come from `Time::from_consensus(...).unwrap()` on real clock values at
  `node/src/lib.rs:369-371`.

---

### Row 6 — `block_header.merkle_root`

- **Field**: `node/src/bead/mod.rs:44`. Produced at `node/src/stratum.rs:1128-1130` from
  `calculate_merkle_root(coinbase_txid, merkle_branches)`.
- **Reaches**: `verify_fee_commitment:80`, `verify_fee_against_template:497`,
  `TemplateEntry::matches:472`, `TemplateCache::template_for:589`.
- **Current binding**: it is in the hash preimage, so it is **pre-committed to the PoW** — but
  G2/G3 mean no PoW is checked at ingest, so today it is simply attacker-chosen. Even with a
  PoW check it is only pre-committed, never *correct*: the miner picks it freely before hashing.
- **Attack**: see Row 2 — `merkle_root` is the output the miner solves for, not a constraint.
  With no PoW check at ingest the attacker sets it to any value at zero cost, so the fold is
  satisfiable for free; with a PoW check the attacker pays one weak share, which they were
  going to pay anyway, and the fold is still satisfiable for free.
- **Detectable?** **No** as a value in isolation. The only thing a verifier can test is
  consistency with a *verifier-derived* pair (coinbase, branch), which is Row 2's check.
- **Check**: PoW first — `weak_target.is_met_by(compute_block_hash(header, network))` — then
  the reconstructed fold. Without the PoW check every "merkle-bound" claim in the design is
  vacuous.
- **Failure response**: PoW failure → **reject** (the producer path only emits beads that met
  the target, `node/src/stratum.rs:1142`). Fold failure → see Row 2.

---

### Row 7 — `block_header.prev_blockhash`

- **Field**: `node/src/bead/mod.rs:44`; produced at `node/src/stratum.rs:1079-1085` (byte-swapped
  from the template's `previousblockhash`) and `:1132`.
- **Reaches**: `verify_fee_against_template:489-494` (anchor equality),
  `TemplateCache::template_for:587` (cache partition key), `TemplateCache::insert:562-566`
  (`(prev_blockhash, BranchKey)` key). Under design §2.4 it scopes the entire cmempool state
  and under `ChainAnchor` (`:394-413`) it fixes the height and hence the subsidy.
- **Current binding**: in the hash preimage (pre-committed, subject to the PoW caveat).
  Never compared against the node's own chain tip anywhere in the tree.
- **Attack**: two.
  (a) **Epoch replay.** Commit a `prev_blockhash` from `k` blocks ago, so the state scope
  (§2.4) resolves to an old epoch in which a large fee was still unconfirmed, and claim it
  again. Each replayed epoch re-credits its whole fee total; with a decay window of ~5 cohorts
  at the default `r = 80/100` (`node/src/edca/mod.rs:38-41`), and realistic epochs being long
  relative to cohorts, the attacker can keep a stale-epoch bead scoring until it decays out.
  Gain is bounded by the largest fee ever present in a retained epoch, not by anything the
  verifier enforces.
  (b) **Cache partitioning / state exhaustion.** Under route 3,
  `TemplateCache::template_for` filters on `prev_blockhash` equality, so a bogus value
  guarantees `Unknown → F_i = 0` — harmless to the attacker's own score but a way to force the
  verifier through the full `BTreeMap` iteration (see §D). Under the universal scheme a
  never-seen `prev_blockhash` means "state unknown" → §2.9 defers → unbounded orphan growth.
- **Detectable?** **Yes**, with the node's own bitcoind: `prev_blockhash` must be a block the
  node knows. **Only-if** the node keeps a short window of recent and stale tips, to avoid
  rejecting honest beads during a block race.
- **Check**: `prev_blockhash ∈ {node's chain tip} ∪ {last K ancestors} ∪ {known stale tips}`
  — one `getblockheader` or an in-memory set, no full round-trip if cached. Then
  `prev_blockhash` must agree with every parent's epoch (§C2). At ingest, before any
  state derivation, because it selects which state to derive.
- **Failure response**: unknown hash → **defer** (an honest bead mined on a block this node has
  not yet seen is normal and common; rejecting forks the DAG). Hash known but older than the
  retention window → **score-at-zero**, do not reject: the bead is a legitimate historical
  share, it just must not re-earn an expired epoch's fees.

---

### Row 8 — `block_header.version`

- **Field**: `node/src/bead/mod.rs:44`; produced at `node/src/stratum.rs:1070-1078`
  (template version, optionally version-rolled under the negotiated mask) and `:1132`.
- **Reaches**: `verify_fee_commitment:87-94`, via
  `Block{header, txdata:[coinbase]}.bip34_block_height()`. BIP34 height extraction is gated on
  `version ≥ 2`; for `version < 2` the call returns `Err(Unsupported)` and route 1 fails with
  `InvalidBip34Height`.
- **Current binding**: in the hash preimage (pre-committed, PoW caveat). Never compared to the
  template's version or to the version-rolling mask by any verifier.
- **Attack**: route 1 derives `subsidy := block_subsidy_sats(height)` from a height read out
  of the **miner's own coinbase scriptSig**, then `derived_fee := coinbase_value − subsidy`
  (`:95-111`). `version ≥ 2` plus a scriptSig height of `≥ 64 × 210_000 = 13_440_000` makes
  `block_subsidy_sats` return 0 (`:24-28`), so `derived_fee == coinbase_value`, and the miner
  sets `coinbase_value` to anything up to the `MAX_MONEY` filter at `:103`. `FeeCommitment`
  then reports `fee_total_sats = 2.1e15` and the equality check at `:113` passes because both
  sides are the miner's. **A_i/A_honest ≈ 6.3e6.** Note the producer's own
  `encode_bip34_height` caps at `MAX_BITCOIN_HEIGHT = 10_000_000`
  (`node/src/template_creator.rs:32,137`) but the *verifier* applies no cap, so the cap is
  decorative. Setting `version < 2` instead is a self-denial (route 1 errors), not an attack.
- **Detectable?** **Yes**, with the node's own bitcoind: the true height is one past
  `prev_blockhash`, which the node knows. Also **Yes** from the DAG alone once `prev_blockhash`
  is validated (Row 7), since height is a function of it.
- **Check**: never read a height from miner data. Derive `height` from the node's own view of
  `prev_blockhash` (`ChainAnchor::new`, `:404-412`, already has the right shape) and require
  `version` to be the template version modulo the version-rolling mask.
- **Failure response**: route 1 should be **deleted, not fixed** — it checks miner data against
  miner data and no repair makes it sound. If retained for the roster path, height mismatch →
  **reject**; honest beads carry the template height.

---

### Row 9 — `block_header.bits` (and, jointly, `committed_metadata.weak_target`)

- **Field**: `bits` at `node/src/bead/mod.rs:44`, produced at `node/src/stratum.rs:1135`
  (`submitted_job.blocktemplate.bits`). `weak_target` at
  `node/src/committed_metadata/mod.rs:77`, produced at `node/src/lib.rs:364` as a **hardcoded
  `1d00ffff`**.
- **Reaches**: `block_probability_q` → `node/src/edca/score.rs:92-104`; the result multiplies
  `A_i` at `raw_score` (`:119-123`) and thus scales the fee claim.
- **Current binding**: `bits` is in the hash preimage (pre-committed, PoW caveat) but is never
  compared to the node's own `getblocktemplate.bits`. `weak_target` is in neither the hash nor
  the merkle root and is **never validated against the header hash anywhere** (G3).
- **Attack**: `score.rs:97-99` returns `ONE` (probability exactly 1) whenever
  `weak_target ≤ bits` as `Target`s, i.e. whenever the committed weak target is *harder* than
  the header's claimed network target. Commit a hard `weak_target` and an easy `bits` and the
  bead scores `S_i = 1 × A_i` instead of `S_i = (T_net/T_bp) × A_i`. For honest weak shares
  ~1e6× easier than network, that is a **1e6× inflation of `S_i` on its own**, and it
  *multiplies* Row 1's 6.3e6×: combined `S_i = 2.1e15` against an honest pool of
  `10^4 × 332 = 3.3e6` q-sats, a ratio of ~**6e8×**. One bead with no work at all takes the
  entire payout.
- **Detectable?** **Yes** for `bits`: the node's bitcoind knows the real `nBits` for the epoch
  of `prev_blockhash`. **Yes** for `weak_target`: the bead's own header hash either meets it
  or does not — a self-contained check needing nothing but the bead.
- **Check**: (i) `weak_target.is_met_by(compute_block_hash(&bead.block_header, network))`;
  (ii) `header.bits == node_bits_for(prev_blockhash)`; (iii) `min_target ≤ weak_target < bits`
  as an ordering invariant; (iv) reject `weak_target == Target::ZERO` rather than skipping the
  bead (`state.rs:99-102` currently `continue`s past it, silently excluding it from scoring
  while leaving it in the DAG). All at ingest, all O(1), (i) and (iii) need no bitcoind.
- **Failure response**: **reject** all four. Honest beads cannot trigger (i) — the producer
  only emits beads whose hash met the target (`node/src/stratum.rs:1142`) — nor (ii), since the
  producer copies the template's bits, except across an epoch boundary, which Row 7's
  `prev_blockhash` scoping resolves. This is O6 in the design doc; it shares the ingest point
  with the fee check and is strictly cheaper than it, so it should land first.

---

### Row 10 — `block_header.time`, `block_header.nonce`

- **Field**: `node/src/bead/mod.rs:44`; produced at `node/src/stratum.rs:1134,1136`.
- **Reaches**: the bead hash only. No fee-path consumer.
- **Current binding**: hash preimage. `time` is `CHECK`-constrained to a u32 range in the DB
  schema (`node/src/db/schema.sql:9`) and nowhere else.
- **Attack**: with no PoW check these are free grinding space, but there is nothing to grind
  *for* in the fee path, since the fold is satisfiable without search (Row 2). Once a PoW check
  exists, an unbounded `time` lets the attacker mine far-future or far-past shares; relevant to
  share-rate accounting, not to `F_i`.
- **Detectable?** **Yes** — median-time-past and a forward tolerance, both from the node's
  own chain.
- **Check**: `prev_block.mtp < time < now + 2h`, at ingest, O(1).
- **Failure response**: **reject** forward-dated beyond tolerance; **accept-and-log** mildly
  stale, since clock skew across honest miners is real and rejecting forks the DAG.

---

### Row 11 — `uncommitted_metadata.extra_nonce_1`, `extra_nonce_2`

- **Field**: `node/src/uncommitted_metadata/mod.rs:14-15`, both `u64`.
- **Reaches**: nothing in the fee path today. Design §2.8 makes them the only miner-supplied
  inputs to the reconstructed coinbase txid, hence to the fold, hence to `F_i`'s attribution.
- **Current binding**: none. Not in the hash preimage (uncommitted by name and by G1), not in
  the merkle root. Decoded at `:50-51` with no checks. DB round-trip is
  `hex::encode(u64::to_be_bytes)` → `u64::from_str_radix(.., 16)`
  (`node/src/db/db_handlers.rs:645-659`), lossless for a `u64` but **the byte length is gone**.
- **Attack**: §2.8 claims en1/en2 "need no authentication: alter them and the reconstructed
  txid changes, the fold fails, the bead self-rejects". That argument is sound **only if the
  byte-level layout is unambiguous**, and it is not (G13). The coinbase is assembled as
  `coinbase1 ‖ hex(extranonce1) ‖ extranonce2 ‖ coinbase2`
  (`node/src/stratum.rs:1105-1111`), where `extranonce1` is a `Vec<u8>` of 8 bytes in direct
  mode (`node/src/lib.rs:118`) but **4** bytes upstream (`node/src/stratum.rs:40`) and
  arbitrary in proxy mode (`:3529`). A remote verifier gets only two `u64`s and cannot know
  whether to serialise them as 4+8, 8+8 or 8+4 bytes — Stratum negotiates the size
  per connection, and it is not in the bead. Each candidate layout yields a different
  `expected_txid` and therefore a different fold result, so either the verifier tries all
  layouts (multiplying the work per bead, §D) or honest beads from differently-configured
  nodes fail reconstruction. A miner can also shift bytes between the node-derived prefix and
  the extranonce window, altering the part the verifier thought it controlled — §2.8 names
  this and it is real.
- **Detectable?** **Only-if** the window length is protocol-fixed or carried in the bead.
  From a bead alone today: **No**.
- **Check**: carry `extranonce1_len`/`extranonce2_len` (or fix both at 8 bytes protocol-wide
  and reject any negotiated size that differs) and change the bead fields to length-explicit
  byte vectors. This is a **protocol change**, not a validation — see §B.
- **Failure response**: n/a today. Once §2.8 is implemented: reconstruction mismatch →
  **score-at-zero**, not reject, until O1 is closed, because an honest bead from a node whose
  coinbase prefix this verifier cannot derive fails identically.

---

### Row 12 — `committed_metadata.payout_address`

- **Field**: `node/src/committed_metadata/mod.rs:71`, a bare `String`; produced from the
  Stratum `worker_name` at `node/src/lib.rs:354` (**note**: the worker name, not a validated
  address).
- **Reaches**: `EdcaState::from_braid` `node/src/edca/state.rs:114` — it is the `MinerKey`,
  i.e. the **beneficiary** of whatever `A_i` the bead earns, and the key of the payout map
  consumed by `miner_totals` (`:206-225`).
- **Current binding**: none. No length bound, no address parsing, no network check, not in the
  hash, not in the merkle root. DB stores it as a BLOB (`node/src/db/schema.sql:13`).
- **Attack**: in scope here because it determines who receives the inflated share. Two effects:
  (a) the attacker directs Row 1/Row 9's inflated weight to any key they like, including a
  *victim's* address, so the inflation is not even attributable to them;
  (b) `MinerKey = String` (`node/src/edca/state.rs:12`) is unbounded, and `scores` is a
  `BTreeMap<String, u128>` cloned per `miner_totals` call (`:220`) — N beads with N distinct
  multi-kilobyte payout addresses give O(N) unbounded map growth per cohort.
- **Detectable?** **Yes** — parse it as an address for the configured network and bound its
  length.
- **Check**: `Address::from_str(..).require_network(..)` at ingest, plus a hard length bound at
  decode.
- **Failure response**: **reject** unparseable. Honest producers pass the Stratum worker name,
  which today may well *not* be an address — so this check would reject beads the current
  producer emits. That is a producer bug to fix first (`node/src/lib.rs:354`), not a reason to
  skip the check; shipping the check without fixing the producer would fork the DAG.

---

### Row 13 — `committed_metadata.comm_pub_key` + `uncommitted_metadata.signature`

- **Field**: `node/src/committed_metadata/mod.rs:72` and `node/src/uncommitted_metadata/mod.rs:17`.
- **Reaches**: nothing. Decoded (`committed_metadata:136-142`, `uncommitted_metadata:59-64`),
  persisted, and never verified.
- **Current binding**: structural validity only (`PublicKey::from_slice`,
  `Signature::from_str`). Both are **hardcoded constants** on the producer side:
  the pubkey at `node/src/lib.rs:338-340` and the signature at `node/src/lib.rs:384-389`.
- **Attack**: because nothing is verified, the pair provides no authentication for the whole
  `committed_metadata` group — which is precisely why Rows 1, 9 and 12 have no binding at all.
  This is the structural reason the fee claim is unauthenticated (O7).
- **Detectable?** **Yes** — trivially, once a signature over `committed_metadata` is actually
  produced and checked.
- **Check**: sign the `committed_metadata` serialisation with `comm_pub_key` and verify at
  ingest; additionally bind `comm_pub_key` to a pool-registered miner identity, otherwise the
  signature authenticates an attacker-chosen key and proves only "whoever made this bead also
  made this claim" — non-repudiation, not correctness.
- **Failure response**: **reject** invalid signature, once producers sign. Today every bead in
  the tree carries the same constant signature, so enabling verification now rejects
  everything.

---

### Row 14 — node-local: `TemplateEntry.fee_total_sats` from bitcoind `components.fees`

- **Field**: `node/src/lib.rs:228-234` — `components.fees.iter().fold(0u64, saturating_add)`.
  Mirrored in `TemplateEntry::new` (`node/src/edca/validate_fees.rs:437-441`), which correctly
  uses `checked_add` plus a `MAX_MONEY` filter.
- **Reaches**: `BlockTemplate.fee_total_sats` → `node/src/stratum.rs:1007` → the bead's
  committed field → the amplifier.
- **Current binding**: trust in the node's own bitcoind. The `saturating_add` at
  `node/src/lib.rs:233` is the weak point: it is the only path that can produce
  `fee_total_sats > MAX_MONEY` (G8), and it does so silently.
- **Attack**: not a miner attack — a **misconfiguration / compromised-IPC** attack. A bitcoind
  (or an IPC man-in-the-middle) reporting absurd per-tx fees makes this node *originate* beads
  whose `fee_total_sats` is `u64::MAX`. Those beads skip the `Decodable` range check entirely
  and propagate. Downstream peers' decode *does* catch them (`:147-153`), so the beads are
  dropped by everyone else — the originating node silently loses all its shares.
- **Detectable?** **Yes**, locally and for free.
- **Check**: replace `saturating_add` with `checked_add` plus a `MAX_MONEY` filter — exactly
  what `TemplateEntry::new` already does — and refuse to issue a job on an out-of-range
  template.
- **Failure response**: **reject the template** (do not emit the job). No bead involved.

---

### Row 15 — persisted `fee_total_sats` and `transaction_ids` on reload

- **Field**: `Bead.fee_total_sats` column (`node/src/db/schema.sql:18`, `CHECK (>= 0)` only)
  and the `Transactions` table (`:31-35`).
- **Reaches**: `build_bead_from_row` `node/src/db/db_handlers.rs:625-629` and
  `fetch_bead_by_bead_hash` `:727-734`, both into `committed_metadata.fee_total_sats`;
  `transaction_ids` repopulated at `:483-515`.
- **Current binding**: `u64::try_from(i64)` — rejects negatives, admits up to
  `i64::MAX ≈ 9.2e18`, i.e. **4,400× `MAX_MONEY`**. The `Decodable` `MAX_MONEY` check is not
  re-applied (G8). Design §2.10 proposes to *write the verified `F_i` to the bead record and
  have the amplifier read the stored value* — so this row is the trust boundary that proposal
  depends on, and it is currently unchecked.
- **Attack**: anything that gets a large value into the column (Row 14's local origination, a
  schema migration, direct DB access, or a future writer) is laundered into a trusted
  `F_i` on restart with no re-validation. Combined with §2.10 the stored value is *by design*
  not re-derived, so there is no second line of defence.
- Separately, **`transaction_ids` order is not preserved**: the reload `SELECT` has no
  `ORDER BY` (G11). If the order differs from the mined order, the merkle root cannot be
  re-derived — every order-sensitive check silently fails after a restart. In practice SQLite
  returns rowid order, which equals insert order (**unverified** that this holds under
  `WHERE bead_id IN (...)` with the `bead_txids` index at `schema.sql:88`, which may well
  drive an index scan in `(bead_id, txid)` order instead — that would be **txid**-sorted, not
  mined order).
- **Detectable?** **Yes** — re-apply the range check on load; add an explicit sequence column.
- **Check**: `fee_total_sats ≤ MAX_MONEY` on load, and `ALTER TABLE Transactions ADD position
  INTEGER` with `ORDER BY position` on reload. Both at the DB boundary.
- **Failure response**: out-of-range on load → **reject the row** and refuse to start rather
  than silently scoring it (a corrupt payout is worse than a failed boot).

---

## A. Hypothesis verdict

### Verdict: **BREAKS.**

Not at the margins and not by a subtle cross-field combination — the central claim is
**vacuous as written**. The repaired version survives, but only after re-admitting the two
things §0 claims to eliminate.

### A.1 The attack

§0 asserts that the tx set is proven by

```
fold(claimed_coinbase_txid, derived_branch) == bead.block_header.merkle_root
```

Count the inputs and who controls each:

| input | controlled by | constraint today |
|---|---|---|
| `claimed_coinbase_txid` = `transaction_ids[0]` | **the miner** | none (Row 2) — 32 arbitrary bytes, never compared to the txid of any transaction |
| `derived_branch` | the verifier | derived from candidate `S(X)` — but **public**: anyone who can derive `S(X)` can derive `branch(S(X))` |
| `header.merkle_root` | **the miner** | in the hash preimage, therefore pre-committed — but freely chosen *before* hashing |

The fold is a **forward computation**, not a constraint. The miner's algorithm:

1. pick any legal parent set `P`; derive `S(X) = ∪S(P) ∪ delta` — the same derivation the
   verifier will do, from the same public DAG;
2. compute `B := branch(S(X))`;
3. pick `c :=` any 32 bytes;
4. set `header.merkle_root := fold(c, B)`;
5. mine that header and set `transaction_ids[0] := c`.

Then `fold(c, B) == merkle_root` holds **by construction**, for every `S(X)` in the candidate
space, at no cost beyond the one weak share the miner had to find anyway. The miner needs no
coinbase transaction, no transaction set, no mempool and no bitcoind. `root_from_branch`
(`node/src/edca/validate_fees.rs:385-391`) performs exactly this forward fold and compares; it
has no way to tell that `c` is not a txid of anything, because the bead carries no
transactions (`node/src/bead/mod.rs:43-47`) and nothing in the tree recomputes a coinbase txid
from a transaction for a peer's bead.

The degenerate instance needs no branch at all: `root_from_branch(c, [])` returns `c`
unchanged (`:386-390`), and `bitcoin::merkle_tree::calculate_root` returns a single leaf
unchanged (G7). So `transaction_ids = [c]` with `merkle_root = c` satisfies both the fold and
route 1's full root recomputation (`:74-85`) for any `c` whatsoever.

### A.2 What the fold actually proves, stated precisely

- **It is a binding.** Under collision resistance of `sha256d`, a share cannot be re-attributed
  after hashing to a different candidate set `S'` with `branch(S') ≠ branch(S)`. The claim is
  **pre-committed**.
- **It is not a proof of possession.** It does not show the miner held the transactions, built
  a coinbase, or could produce a block. It shows only that the miner knew `branch(S(X))` —
  which is public data derivable from the DAG by anyone, including an attacker with no
  transactions at all.
- **It does not pin the leaf count.** `calculate_root` duplicates the last element on odd
  counts (G7), so `[c,t1,t2]` and `[c,t1,t2,t2]` share both the root *and* the coinbase branch
  `[t1, H(t2‖t2)]`. The branch length the verifier checks against is the length the *verifier*
  chose; the fold confirms nothing about how many leaves the miner's tree had. Pinning leaf
  count needs an explicit `transaction_ids.len() == 1 + |S(X)|` plus duplicate rejection, which
  the fold route has neither of (`verdict` reads only element 0, `:606`).
- **Today it does not even bind.** G2/G3: `Braid::extend` checks no proof of work, so the
  header's merkle root is not anchored to anything. "Pre-committed to the PoW" is an empty
  phrase until a PoW check exists at ingest.

So §0's "the non-coinbase leaves are exactly `S(X)` in canonical order" is a category error:
the bead has no leaves. It has a root (unconstrained), a claimed coinbase txid
(unconstrained), and a list of 32-byte strings that the fold route never reads.

### A.3 Why this makes §0's conclusion self-defeating

§0's stated payoff is: *"no coinbase reconstruction is needed for fee validation, no cache of
node-local coinbase material is needed, and O1's global-key/local-value problem does not arise
in the fee path at all. Fee validation becomes universal and cacheless."*

Coinbase reconstruction (§2.8) is **precisely what gives the fold content**: it replaces the
miner-chosen left leaf with a value the verifier computes itself, which is the design's own
rule §1.2 (*"a verifier may accept miner-supplied data only when it reduces to a value the
node independently holds"*). `claimed_coinbase_txid` does not reduce to any value the node
holds. §0 therefore violates §1.2 in the same move that it cites it.

And the reconstruction the fold needs is exactly the node-local material O1 is about: the
coinbase prefix depends on the issuing node's pool tag, height view and extranonce sizing, and
the suffix on its `EdcaConfig`, output budget and address resolution (§2.5). So the fee path
becomes "universal and cacheless" only by deleting its one real check, and re-adding the check
drags O1 straight back in. **§0 does not dissolve O1 in the fee path; it hides it.**

### A.4 An independent second break: proving the set does not bound `F_i`

Even granting a perfect set proof, `F_i = Σ fees over S(X)` is unbounded, because `S(X)` is
miner-steerable at near-zero cost:

- `parents` (Row 4) and `delta = additional_tx_ids` (§2.1) are both miner-chosen and
  unvalidated; `delta` admits 2..5 transactions with **no bound on their fees**.
- The attacker constructs a valid transaction spending their own output almost entirely to fee
  — e.g. 10 BTC in, 1 sat out, `F ≈ 1e9` sats — and places it in their own `delta`. Under §2.2
  `delta(X) ⊆ S(X)`, so the fee is credited to the attacker's own bead immediately.
  `A_i = 3.125e8 + 1e9 = 1.31e9`, i.e. **3.9×** honest, per bead, repeatable.
- The fee is only ever *paid* if some block confirms the transaction. The attacker prevents
  that: RBF-replace it on the real Bitcoin network, or double-spend the prevout. The cmempool
  is DAG-derived, not mempool-derived (§2.2), so the transaction stays in `S(X)` until the
  epoch reset — this is O2, and O2 is what makes the attack free.
- If the attacker's own bead does meet network difficulty, they simply do not publish the
  block, forfeiting one subsidy while retaining the inflated share across the whole retention
  window.
- Scaling: `F → MAX_MONEY` gives `A_i/A_honest ≈ 6.3e6`; against a window of 10,000 honest
  beads the single bead takes **99.84%** of the pool's entire payout.

This is invisible to the fold, to every single-field check, and to a *correct* set proof. It is
a protocol-economics gap, not a validation gap, and it means the fee path needs a bound on `F`
that does not come from set membership.

### A.5 The surviving fragment

One part of §0 does survive and is worth keeping explicitly:

> `F_i` is computed by the verifier from its own `S(X)`, never read from the bead.

That is sound and it is the single most valuable idea in the document. A tx fee is objective
(`inputs − outputs`, `node/src/edca/validate_fees.rs:193-238`), so every node holding the
transaction and its prevouts computes the same number, with no cache and no node-local state.
For the fee **number**, O1's global-key/local-value problem genuinely does not arise. What does
not survive is the claim that the *attribution* of a bead to an `S(X)` is free of coinbase
reconstruction.

### A.6 Required conditions for a repaired hypothesis

If §0 is restated as *"`F_i` is computed by the verifier from a uniquely-determined `S(X)`, and
a bead is attributed to an `S(X)` by folding a **verifier-reconstructed** coinbase txid up a
verifier-derived branch to the work-bound root"*, it survives — under all seven of these,
each a required check:

| # | Condition | Without it |
|---|---|---|
| **C1** | The fold's left input is **reconstructed**, never accepted: `expected_txid = txid(derived_prefix ‖ en1 ‖ en2 ‖ derived_suffix)`. Needs the extranonce window length protocol-fixed or carried in the bead (Row 11) and the prefix/suffix DAG-derivable (O1(a)) or carried (O1(b)). | §A.1 — the fold is satisfiable for free, for any set, with no transactions. |
| **C2** | `F_i` is never read from the bead; `fee_total_sats` is only ever compared, with `claim > computed` on a complete set as a reject. `verify_fee_bound`'s `saturating_add` (`:331`) must become `checked_add`, and it must **deduplicate** txids (see §C4). | Row 1 — unbounded `A_i` from a bare integer. |
| **C3** | `S(X)` is **uniquely** determined by the DAG: O4 canonical order pinned byte-exactly, O3 double-spend tiebreak, O2 eviction reconciliation, plus structural parent validation (Row 4) and a validated `prev_blockhash` epoch (Row 7). | Honest beads mismatch, defer forever, orphan pool grows unbounded (§D). Non-unique `S(X)` also lets a miner pick among candidate sets post hoc. |
| **C4** | `F_i` is bounded **independently of set membership** — e.g. credit `additional_tx_ids` fees only after confirmation, or cap `F_i` at a multiple of the epoch's median template total. | §A.4 — free, repeatable, unbounded inflation through self-paying unconfirmable transactions. |
| **C5** | **PoW is checked at ingest** (`weak_target.is_met_by(bead_hash)`), `weak_target != 0`, `min_target ≤ weak_target < bits`, and `bits` equals the node's own epoch `bits`. | Row 6/Row 9 — "pre-committed" has no anchor, and the probability factor collapses to `ONE` for a 1e6× score multiplier that *multiplies* any fee inflation. |
| **C6** | `transaction_ids.len() == 1 + \|S(X)\|`, no duplicate txids, and `transaction_ids[1..] == canonical_order(S(X))` element-wise. | The fold does not pin leaf count (G7); duplicates inflate `verify_fee_bound` linearly (§C4). |
| **C7** | Decode is hardened: bounded declared lengths, no `.unwrap()` on `Time::from_consensus`. | G9/G10 — the node is killed by a 40-byte message before any of the above runs. |

Note that C1 and C3 together reintroduce node-local coinbase material and a canonical-ordering
consensus object into the fee path — the two things §0 set out to remove. The honest summary is
that **fee validation is not cheaper than roster validation; it is the same problem minus the
output values.**

---

## B. Unvalidatable residue

Inputs for which **no check is possible from a bead alone**, with the minimum protocol change
each would need. This is the lower bound on what the wire format must carry for fees to be
verifiable at all.

| Input | Why no check exists | Minimum protocol change |
|---|---|---|
| `transaction_ids[0]` — the coinbase txid | The bead carries no coinbase (`node/src/bead/mod.rs:43-47`); the coinbase of an unbroadcast weak share is in no mempool and no chain, so neither DAG state nor bitcoind can witness it. | **Either** (a) make the coinbase fully DAG-derivable — consensus-fix pool tag, BIP34 height source, extranonce sizing, `EdcaConfig`, output budget and address-resolution rules (O1(a)) — **or** (b) carry `coinb1`/`coinb2` (or a commitment to them) in the bead, costing ~100–200 bytes (O1(b)). Nothing cheaper works: the left leaf must reduce to a value the verifier holds. |
| Extranonce window layout | Stratum negotiates `extranonce1`/`extranonce2` sizes per connection (`node/src/stratum.rs:3529`, `:40`, `node/src/lib.rs:118,124`); the bead carries two bare `u64`s (G13) and a remote verifier cannot know the byte widths. | Carry explicit `extranonce1_len`/`extranonce2_len`, or change the fields to length-prefixed byte vectors, or fix both at 8 bytes protocol-wide and reject any other negotiated size at the Stratum boundary. |
| Whether the miner **held** the transactions in `S(X)` | Fundamentally unprovable from a bead: possession is not a property of any 32-byte digest. | Accept the design's own answer (§2.11): the verifier fetches the transactions itself and **defers** when it cannot. That converts an unprovable property into an availability requirement — and into the DoS in §D.5. A succinct proof of possession would need the bead to carry the txs or an accumulator witness; neither is cheap. |
| Whether `F_i`'s fees will ever be **paid** | Whether an unconfirmed transaction ever confirms is unknowable at bead time, by anyone. | Either credit `additional_tx_ids` fees only after confirmation (delays the incentive §2.1 is built on), or cap `F_i` relative to an epoch-wide observable. There is no third option. |
| `weak_target` as an *entitlement* | The bead's hash either meets `weak_target` or not — that part **is** checkable from the bead alone. What is not checkable is whether the miner was *allowed* to choose that target; nothing in the DAG assigns difficulties. | A pool-signed difficulty assignment carried in the bead, or a DAG-derived difficulty rule (e.g. `weak_target` fixed per epoch by a rule every node computes). Until then `weak_target` is self-assigned, and O8's "distinct weak targets" warning (`node/src/edca/state.rs:131-137`) is the symptom. |
| `payout_address` as an *entitlement* | A parseable address proves nothing about who is entitled to it; the field is also the inflated share's destination (Row 12). | A signature over `committed_metadata` by a `comm_pub_key` bound to a pool-registered miner identity (O7). Signing alone gives attributability, not correctness — it tells you *who* lied. |
| `fee_total_sats` after a restart, under §2.10 | §2.10 deliberately stores the verified `F_i` and does not re-derive it; the DB load applies no `MAX_MONEY` check (Row 15, G8). | Either re-derive on load (which defeats §2.10's purpose) or treat the DB as part of the trust boundary and re-apply the range check plus an integrity check at load. |
| `parent_bead_timestamps` | Never persisted; reload substitutes the parents' own `start_timestamp` (Row 4). Even a signature over `committed_metadata` would fail for every reloaded bead. | Persist the committed vector verbatim with an explicit position, before any signature over `committed_metadata` is introduced. |

---

## C. Cross-field attacks

Combinations where each field is individually plausible and passes every per-field check, but
the combination is impossible for an honest producer. Single-field validation misses all of
these.

### C1 — `fee_total_sats` vs `transaction_ids`: never jointly checked

The two fields are **never compared to each other anywhere in the tree**. Route 1 compares
`fee_total_sats` against the *coinbase value minus a miner-supplied subsidy*
(`node/src/edca/validate_fees.rs:106-118`), not against the transactions. Route 3 compares it
against a cached template total (`:504-510`) and ignores the list entirely. `verify_fee_bound`
is the only function that touches both, and it has **zero callers** (G5).

Attack: `transaction_ids = [cb]` (a one-element list — plausible, an empty template) together
with `fee_total_sats = 2.1e15` (plausible, it passes the `MAX_MONEY` decode check). Jointly
impossible: a template with no transactions has zero fees.

Check: the invariant `fee_total_sats == 0 ⟺ transaction_ids.len() == 1`, strengthened to
`fee_total_sats ≤ Σ fee(tx) for tx ∈ transaction_ids[1..]` whenever the verifier knows all of
them. O(1) for the first form, no bitcoind needed.

### C2 — `prev_blockhash` vs parents' epoch: stale-epoch fee replay

`prev_blockhash` is a real block hash (passes Row 7's membership check). `parents` are real
current tips (pass Row 4's presence check). Neither field alone is suspicious. Jointly they are
impossible: a bead's header came from a job issued on the template for `prev_blockhash`, and
at that moment the tips were that epoch's tips — a bead cannot simultaneously be mined on epoch
`H−5`'s template and witness epoch `H`'s beads as parents.

Gain: under §2.4 the cmempool state is scoped to `prev_blockhash`, so this lets the attacker
select the *epoch* whose fee landscape they claim, picking the one that held the largest
unconfirmed fee, while still attaching to the current tips so the bead lands in a scoring
cohort. Each replay re-credits that epoch's fee total.

Check: every parent's `prev_blockhash` must equal the bead's, or be its immediate predecessor
across exactly one boundary; and `bead.block_header.time` must postdate every parent's. Pure
DAG-local, O(|parents|), no bitcoind.

Honest-bead risk: real during a block race, when honest beads straddle a boundary — hence
"equal, or predecessor across one boundary", and **defer** rather than reject (Row 7).

### C3 — `weak_target` × `fee_total_sats`: the multiplicative attack

Each field is individually in range: `weak_target` is a valid `CompactTarget`,
`fee_total_sats ≤ MAX_MONEY`. The product is what matters, and nothing computes a bound on the
product. `raw_score` (`node/src/edca/score.rs:119-123`) is literally
`probability × A_i`, and the attacker controls both factors:

- `probability = ONE` by committing `weak_target ≤ bits` (`score.rs:97-99`, Row 9) — a 1e6×
  gain over an honest weak share;
- `A_i = 2.1e15` by Row 1 — a 6.3e6× gain.

Combined `S_i = 2.1e15` q-sats against an honest pool of `10^4 × 332 = 3.3e6` q-sats: a ratio
of ~**6e8**. One bead, requiring **zero** proof of work (G2), captures the entire pool payout
for the whole retention window. Any check on either field alone leaves a 1e6× hole.

Check: both of Row 9's checks plus Row 1's, and they must land together. The `weak_target`
check is strictly cheaper (one sha256d, no bitcoind) and should land first.

### C4 — duplicate txids vs the derived branch: linear fee inflation in `verify_fee_bound`

`verify_fee_commitment` deduplicates (`:69-72`). `verify_fee_against_template` does **not** —
it never looks past element 0. `verify_fee_bound` consumes a `FeeCommitment` produced by
*either*, and sums **per occurrence** with no dedup:

```rust
for txid in bead.committed_metadata.transaction_ids.0.iter().skip(1) {   // :329
    match fees.fee_sats(txid) {
        Some(fee) => computed_fees = computed_fees.saturating_add(fee),  // :331
```

So on the `verify_fee_against_template → verify_fee_bound` path, a bead listing one high-fee
txid 100 times gets `computed_fees = 100 × fee` and `verify_fee_bound` returns
`FeeBound::Proven` for a claim 100× the truth. The `saturating_add` compounds it: a list long
enough to saturate at `u64::MAX` satisfies `computed_fees >= commitment.fee_total_sats`
(`:336`) for **any** claim, so `Proven` is returned for `fee_total_sats = MAX_MONEY` with no
real fees at all. Both defects are in the one function the design nominates as "the right
check".

Separately, the CVE-2012-2459 shape (G7) means `[cb,t1,t2]` and `[cb,t1,t2,t2]` share the root
*and* the coinbase branch, so the fold cannot distinguish them — the only thing that can is an
explicit `len == 1 + |S(X)|` plus dedup.

Check: dedup before summing, `checked_add` not `saturating_add`, and C6 from §A.6.

### C5 — duplicate txid vs the persistence layer: a one-bead consensus split

This one crosses the bead/DB boundary and is the most consequential cross-field finding after
§A.

1. A bead with a duplicate txid passes `Braid::extend` — no duplicate check exists there
   (`node/src/braid/mod.rs:90-207`) — and enters the in-memory braid.
2. `persist_added_bead` hands it to `insert_beads_batch` together with every orphan the bead
   just promoted (`node/src/db/mod.rs:49-56`), and the whole call runs inside **one SQL
   transaction** with an explicit `rollback()` on any chunk failure
   (`node/src/db/db_handlers.rs:320-351`). During IBD the batch is up to
   `BATCH_INSERT_THRESHOLD = 500` beads per chunk (`:19`, `:333`).
3. `Transactions` has `UNIQUE (bead_id, txid)` (`node/src/db/schema.sql:34`), so the duplicate
   violates the constraint and **the entire transaction is rolled back** — the malformed bead
   and every bead batched with it.
4. The in-memory braid keeps them all; the DB has none of them. Blast radius is the bead plus
   its promoted orphans on the gossip path, and up to the whole batch during IBD.
5. Worse, it is **permanent for the descendant subtree**: `Relatives.child/parent` and
   `ParentTimestamps` FK-reference `Bead(id)` (`node/src/db/schema.sql:63-76`) and
   `foreign_keys(true)` is set in production (`node/src/db/init_db.rs:51`). With the malformed
   bead's `Bead` row rolled back, every later descendant's `Relatives` insert fails the foreign
   key and rolls back in turn. One malformed bead silently poisons persistence of everything
   mined on top of it.
6. Different nodes batch differently and promote different orphans, so different nodes lose
   *different* beads, compute different cohorts, and therefore different EDCA states and
   different payouts.

Attacker cost: one bead with one repeated txid. Effect: a persistent, silent, per-node payout
divergence that only manifests after a restart. Check: reject duplicate txids at decode (C6) —
before the bead can reach either the braid or the DB.

### C6 — `bits` vs `prev_blockhash`

`bits` is a valid `CompactTarget`; `prev_blockhash` is a real block. Jointly: `bits` is a
deterministic function of the epoch of `prev_blockhash`, which the node's bitcoind knows
exactly. A mismatch is impossible for an honest producer, which copies the template's bits
(`node/src/stratum.rs:1135`). This is the cheap half of C3's defence and needs only a cached
epoch→bits map, no round-trip.

### C7 — `payout_address` vs `comm_pub_key`: unattributable inflation

Nothing binds the beneficiary to the signer (Row 12, Row 13). An attacker can direct C3's
inflated weight to a *victim's* payout address, so the pool's own anomaly detection points at
an innocent miner, and banning the beneficiary punishes the wrong party. Check: the signature
over `committed_metadata` must cover `payout_address`, and `comm_pub_key` must be
pool-registered — i.e. O7 is a prerequisite for any abuse response, not just for correctness.

### C8 — decode range check vs the DB round trip

`fee_total_sats ≤ MAX_MONEY` holds on the wire (`node/src/committed_metadata/mod.rs:147-153`)
and not in storage (`CHECK (fee_total_sats >= 0)` only, `node/src/db/schema.sql:18`;
`u64::try_from(i64)` on load, `node/src/db/db_handlers.rs:625-629`). Every value in
`(MAX_MONEY, i64::MAX]` is rejected on the wire and accepted from disk — a 4,400× window that
opens on restart. Under §2.10, where the stored value is authoritative and never re-derived,
this is the whole trust boundary.

---

## D. Griefing and DoS surface

Costs are per bogus bead. "Ratio" is verifier work ÷ attacker work; anything above ~1 is a
griefing vector. A `Bead` on the wire is roughly `80 + 32·|txids| + 32·|parents| + ~250` bytes.

### D.1 Existing vectors, present today, independent of any fee check

| # | Vector | Attacker cost | Verifier cost | Ratio |
|---|---|---|---|---|
| D1a | **`Vec::with_capacity(u64)` in `TxIdVec`/`TimeVec` decode** (`node/src/committed_metadata/mod.rs:31,55`, G9). A declared length of `u64::MAX` asks for 32 × 2^64 bytes before one element is read. | ~40 bytes, one floodsub message, **no PoW** | capacity-overflow abort → process death | **unbounded** |
| D1b | **`.unwrap()` on `Time::from_consensus`** (`:34`, G10). Any `parent_bead_timestamps` entry `< 500_000_000` panics the decoding task inside the swarm event loop (`node/src/main.rs:1143`). | ~250 bytes, **no PoW** | panic → networking (or process) down | **unbounded** |
| D1c | **`extend`'s O(N) duplicate scan**: `self.beads.iter().any(\|b\| self.compute_bead_hash(b) == bead_hash)` (`node/src/braid/mod.rs:123-127`) recomputes a double-SHA256 over **every bead in the braid** on every insert — while `bead_index_mapping` (`:38`), an O(1) hash map keyed by exactly that value, sits unused two lines above. | ~300 bytes | `N` × sha256d(80 B). At `N = 10^6`: ~10^6 × ~0.5 µs ≈ **0.5 s of CPU per bead**, holding the braid write lock | **~10^6 : 1** |
| D1d | **Unbounded orphan pool**: `self.orphan_beads.push(bead.clone())` (`:117`) with no cap, no dedup, and **no PoW check first**. `process_orphan_beads` (`:209-250`) runs on *every* successful extend and rescans the whole vector. | `k` beads naming a nonexistent parent | `O(k)` memory held forever + `O(k)` rescan per subsequent extend → `O(k·m)` CPU for `m` honest beads | memory 1:1, **CPU `O(m)`:1** |
| D1e | **Unbounded `MinerKey`**: `payout_address: String` (Row 12) keys a `BTreeMap` cloned per `miner_totals` call (`node/src/edca/state.rs:12`, `:220`). | one multi-KB string per bead | per-cohort map growth × clone per payout | ~1:1 memory, worse on each payout |

D1a–D1d all sit **in front of** any conceivable fee check, which is why §A.6's C7 is listed as
a condition on the hypothesis rather than as a separate hardening task: the fee check is
unreachable.

### D.2 Cost of the checks this audit proposes

| Check | Verifier work per bead | Attacker work | Verdict |
|---|---|---|---|
| Bounded decode lengths, no `unwrap` | O(bytes read), bounded | O(bytes sent) | 1:1 — safe |
| Structural: duplicate txids, `parents.len() == timestamps.len()`, `fee ≤ MAX_MONEY`, `min_target ≤ weak_target != 0`, address parses | O(\|txids\|) hash-set inserts | O(\|txids\|) bytes | 1:1 — safe |
| **PoW**: `weak_target.is_met_by(bead_hash)` | **1** sha256d | ~2^k hashes for target `k` | **1 : 2^k** — the only check that imposes real cost on the attacker |
| Dedup via `bead_index_mapping` | O(1) | O(1) | safe (and fixes D1c) |
| `prev_blockhash ∈ known blocks`, `bits == epoch bits`, MTP window | O(1), in-memory set | O(1) | safe — **no bitcoind round-trip if the recent-block set is cached** |
| Parents present, epoch agreement, no mutual ancestry | O(\|parents\|) map lookups + memoized ancestor-set intersection | O(\|parents\|) | safe **only with memoization**; without it `get_all_ancestors` (`:622-660`) builds a `HashSet<usize>` per bead → O(N²) memory for a single deep-ancestry bead |
| Derive `S(X)` incrementally from memoized parent states | O(\|delta\|) set inserts | O(1) | safe **only with memoization**; recomputing from the DAG is O(\|ancestors\|) per bead → attacker sends one deep bead, verifier walks the whole DAG |
| `transaction_ids[1..] == canonical_order(S(X))` | O(\|S\|) comparisons, no hashing | O(\|S\|) bytes | 1:1 — safe |
| Reconstructed-coinbase fold | ~log2(\|S\|) ≈ 13–17 sha256d, ~10 µs | O(1) | safe |
| `TemplateCache::template_for` (route 3) | full `BTreeMap` scan filtered on `prev_blockhash`, then up to `MAX_CACHED_TEMPLATES = 90` (`node/src/lib.rs:21`) folds of ~17 sha256d ≈ 0.8 ms. The `BranchKey` half of the map key is never used for lookup (`:584-590`), so the ordering buys nothing. | O(1) | ~10^3:1 — tolerable, but it should look up by `BranchKey` instead of scanning |
| **Fee computation: fetch unknown txs + prevouts** | **the problem** — see D.3 | O(1) | **~10^5 : 1** |

### D.3 The one check that costs the verifier more than the attacker

Per §2.11, ingest must validate each `additional_tx_id` against the state's implied UTXO view,
so the node must obtain the transaction and its prevouts. A bead naming 5 random 32-byte
strings as `additional_tx_ids` costs the attacker **160 bytes** and costs the verifier **5
`getrawtransaction` round-trips minimum** (plus one per input for prevouts, so up to ~500 for
100-input transactions). At ~5 ms per round-trip that is 25 ms–2.5 s of verifier latency per
160-byte message: a ratio of roughly **10^5 : 1**, and it serialises behind the braid write
lock if performed inline.

Mitigations, in order of effectiveness:

1. **Put PoW in front of it.** A weak share is the only cost anchor available; no bitcoind call
   may happen for a bead that has not met `weak_target`. This single ordering change converts
   the ratio from 10^5:1 into `2^k`:1 in the attacker's disfavour.
2. **Defer the fee computation off the ingest path entirely.** Insert the bead with
   `F_i = unknown`, compute `F_i` lazily in a bounded background worker, and score `F_i = 0`
   until resolved. §2.10 already wants `F_i` computed once and stored; computing it
   asynchronously costs nothing extra and removes the round-trips from the hot path.
3. **Bounded negative cache** of txids the node asked bitcoind about and did not find, so the
   same bogus txid is never fetched twice.
4. **Per-peer rate limit** on bead-triggered bitcoind queries, with the existing
   `peer_manager.penalize_for_invalid_bead` (`node/src/main.rs:1602`) extended to peers whose
   beads repeatedly name unknown transactions.
5. **Cap `|additional_tx_ids|`** at the protocol's 5 (§2.1) *at decode*, so the per-bead
   round-trip count has a hard ceiling before anything else runs.

### D.4 DoS-resistant ingest ordering

Strictly cheapest-first, with the rule that **no step may cost the verifier more than the
attacker paid to reach it**, and with the PoW check placed at the point where the attacker's
cost becomes non-trivial:

```
 1. Decode            bounded lengths; no unwrap                      O(bytes), no state
 2. Structural        non-empty parents ≤ K; |parents| == |timestamps|;
                      no duplicate txid; |txids| ≤ 2^17;
                      |additional_tx_ids| ≤ 5; fee ≤ MAX_MONEY;
                      weak_target != 0; min_target ≤ weak_target;
                      payout_address parses                           O(|txids|), no state
 3. PROOF OF WORK     weak_target.is_met_by(compute_block_hash(..))    1 sha256d   <-- cost gate
 4. Dedup             bead_index_mapping lookup (not the O(N) scan)   O(1)
 5. Epoch             prev_blockhash ∈ cached recent blocks;
                      bits == epoch bits; MTP < time < now+2h         O(1), no round-trip
 6. DAG-local         parents present; parents' epoch agrees;
                      no mutual ancestry (memoized)                   O(|parents|)
 7. State             derive S(X) incrementally from memoized parents O(|delta|)
 8. Set equality      txids[1..] == canonical_order(S(X))             O(|S|), no hashing
 9. Fold              reconstructed coinbase txid -> header root      ~17 sha256d
10. Fees              fetch unknown txs/prevouts; F := Σ fee(S(X));
                      reject if claim > F on a complete set           ASYNC + cached + rate-limited
```

Steps 1–2 must never allocate or hash proportionally to an attacker-declared number. Step 3 is
the boundary: everything above it is free for the attacker, everything below it costs them
`2^k` hashes. Steps 5–9 are all node-local and need no external I/O. Step 10 is the only step
that touches bitcoind and it belongs off the critical path.

### D.5 Interaction between §2.9 and the orphan pool

§2.9 is right that unknown state must defer rather than reject — permanent rejection forks the
DAG. But "defer" lands the bead in `orphan_beads`, which is unbounded, un-deduplicated, cloned
in full, and rescanned on every extend (D1d). So the correct policy and the current mechanism
compose into a memory and CPU DoS. Deferral needs:

- a **cap** on the orphan pool with eviction by lowest work (which requires step 3, so PoW
  must be checked *before* parking an orphan — today it is parked at `:117` before any check);
- **dedup** by bead hash on insert;
- a **retry budget** per orphan rather than an unconditional full rescan per extend;
- an **expiry** tied to the epoch reset (§2.4), so a bead whose state will never be derivable
  does not sit forever.

---

## Appendix — defects found that are not themselves attacks

1. `verify_fee_bound`'s `saturating_add` (`node/src/edca/validate_fees.rs:331`) can report
   `Proven` on saturation; must be `checked_add`.
2. `verify_fee_bound` does not deduplicate txids (§C4).
3. `node/src/lib.rs:233` sums bitcoind's per-tx fees with `saturating_add` while
   `TemplateEntry::new` (`:437-441`) does the same sum with `checked_add` + `MAX_MONEY` filter.
   The producer should use the stricter form.
4. `root_from_branch` (`:377-391`) and `calculate_merkle_root`
   (`node/src/template_creator.rs:168-180`) are byte-identical duplicates with no cross-test;
   route 3's entire soundness rests on them agreeing (G6). One should call the other.
5. `TemplateCache::template_for` (`:584-590`) scans linearly and never uses the `BranchKey`
   half of its own map key; a `BranchKey`-indexed lookup would be O(log n).
6. `state.rs:99-102` silently `continue`s past a zero-`weak_target` bead, excluding it from
   scoring while leaving it in the DAG — it should be rejected at ingest instead.
7. `parent_bead_timestamps` is never persisted; reload substitutes the parents' own
   `start_timestamp` (Row 4). Any future signature over `committed_metadata` will fail for
   every reloaded bead.
8. `transaction_ids` has no ordering column and is reloaded by an unordered `SELECT`
   (G11) — every order-sensitive check is unreliable after a restart.
9. `payout_address` is populated from the Stratum `worker_name` (`node/src/lib.rs:354`), not
   from a validated address; it is also the `MinerKey` that receives payouts.
10. `comm_pub_key` and `signature` are hardcoded constants on the producer side
    (`node/src/lib.rs:338-340`, `:384-389`) and verified nowhere (O7).
