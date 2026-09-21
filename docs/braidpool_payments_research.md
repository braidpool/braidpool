# BitVM-Based UHPO Settlement

## 1. Introduction and Problem Statement

In [Payout Authorization](braidpool_spec.md#payout-authorization) we identified
that authorizing the UHPO share payouts is "the largest unsolved problem" facing
Braidpool. Bitcoin cannot evaluate the logic of the pool's consensus mechanism.
We need a way to ensure that the coinbase outputs are spent correctly, paying
all hashers according to the share tally.

The current approach uses [FROST](https://eprint.iacr.org/2020/852) /
[ROAST](https://eprint.iacr.org/2022/550) threshold Schnorr signatures with the
$S$ most recent block winners (approximately 50 signers) to sign each
coinbase's spending transaction. While this is a reasonable starting point, it
has known limitations:

1. **Liveness failures.** A threshold number of signers must remain online
   through the entire DKG and signing process *for every block's coinbase* —
   approximately 2016 signing ceremonies per epoch. If any participant fails,
   the subset must be restarted. With 50 signers, even modest churn rates
   cause frequent restarts.

2. **51% attack on a small signer set.** A miner controlling a fraction $f$ of
   the pool's hashrate has a non-negligible probability of winning enough recent
   blocks to control the signing committee (see
   [51% Attack](braidpool_spec.md#51-attack)).

3. **Non-verifiable key deletion.** After signing, nodes are expected to delete
   their key shares. We cannot verify that deletion actually occurred, leaving a
   window for key recovery and unauthorized spending.

What we need is a mechanism where the *correctness* of payouts can be
cryptographically verified without requiring the signers to compute the correct
payouts themselves. We want to minimize the trust placed in any single party.

## 2. Fundamental Constraints

### 2.1 The Output-Binding Problem

Without output introspection capabilities, Bitcoin Script can only gate on *who
signs* a transaction, not *where funds go*. Script conditions like P2PKH,
P2WPKH, and P2TR all verify that the spender possesses a particular key, but
they cannot constrain the outputs of the spending transaction.

This means that any spending authorization reduces to: "does this key (or
threshold of keys) approve?" There is no way to say "these funds can *only* be
spent to these specific outputs" without cooperative signing.

### 2.2 The Unknown Future Problem

The payout amounts for a given epoch are unknown at coinbase creation time. The
share tally depends on future beads that have not yet been mined, and the fee
reward depends on transactions that will be included in future blocks. CTV
(OP_CHECKTEMPLATEVERIFY) commits to a fixed transaction template, but we cannot
compute that template until the epoch ends.

### 2.3 Other Approaches Considered

**PIPEs v2** (Polynomial Inner Product Encryption) can theoretically enforce
arbitrary spending conditions using functional encryption. However, the
ciphertext for practical key sizes is approximately 338 TB, there is no working
implementation, and like all Script-based approaches, it can gate on key
possession but not output destinations.

**Adaptor signatures** allow conditional signing (revealing a secret upon
signature completion), but again only bind to keys, not to output destinations.

**Direct large multisig** (e.g., CHECKMULTISIG with many keys) is limited to ~20
keys by script size limits and requires all signers to be known in advance.

### 2.4 Implication

All current Bitcoin mechanisms require cooperative signing to authorize
spending. The design space is therefore about *minimizing the trust required* in
the signers. We seek a solution where:

- Correct payouts can be verified by anyone,
- Incorrect payouts can be challenged and proven fraudulent on-chain,
- The signing committee need not compute the payouts themselves.

## 3. The Risk-Taker as Payment Processor

### 3.1 The Derivatives Market

As described in [derivatives.md](derivatives.md), miners can engage in hashrate
derivatives contracts with *risk-takers* who pay a fixed rate per share,
emulating FPPS. The risk-taker is the counterparty in a fixed-for-floating swap:
the miner receives a predictable income, and the risk-taker absorbs the
variance in block rewards and fees.

Risk-takers are well-capitalized entities that audit miners' share production
via Braidpool nodes. They are repeat players with reputational capital, and they
already front capital to miners in exchange for shares.

### 3.2 Natural BitVM Operator

A risk-taker who has purchased shares from miners needs *reimbursement* from
the epoch's coinbase pool for those shares. This makes the risk-taker a natural
[BitVM2](https://bitvm.org/bitvm2) *operator*: they front payouts to miners,
compute the correct UHPO distribution, and then claim reimbursement from the
epoch's coinbase UTXOs, subject to a challenge period where any party can
submit a fraud proof.

The key insight is that the risk-taker is *already paying miners*. The BitVM
settlement merely reimburses them from the epoch's coinbase outputs. This
aligns incentives: the operator wants correct settlement because they have
already laid out the capital.

### 3.3 Multiple Risk-Takers

Multiple risk-takers can operate simultaneously, each serving a subset of
miners. Competition among risk-takers drives down fees. Any well-capitalized
party can act as an operator — the role is permissionless. See
[Section 6](#6-parallel-batched-settlement) for how multiple operators
coordinate.

### 3.4 Non-Derivative Miners

Miners who choose not to engage a risk-taker are still included in the
settlement. The operator computes the UHPO for *all* miners (both derivative
and non-derivative) and pays all of them. Non-derivative miners receive the
floating rate determined by the share formula. Miners who do not trust any
operator may wait for the FROST fallback described in
[Section 7](#7-bootstrapping-and-fallback).

## 4. Protocol Specification

### 4.1 Roles

**Signers Committee (SC).** A set of $S$ miners who pre-sign the BitVM
transaction templates. Following the
[Payout Authorization](braidpool_spec.md#payout-authorization) section of the
spec, these are the unique hashers who won the most recent $S \approx 50$
blocks, with a threshold of $\lceil 2S/3 \rceil + 1$ required to sign. The SC
does not compute payouts; it only enables the dispute mechanism by pre-signing
templates.

**Operator (Risk-Taker).** Proposes a settlement for a completed epoch. The
operator computes the UHPO distribution, pays all miners (derivative and
non-derivative), posts a bond, and claims reimbursement from the epoch's
coinbase UTXOs after a dispute window. This role is permissionless — any well-capitalized party can
propose.

**Challengers.** Verify the operator's proposed settlement and submit fraud
proofs if it is incorrect. Every Braidpool full node is a natural challenger
because all nodes maintain the full DAG state and can independently compute the
correct UHPO. A challenger who successfully disproves a claim receives the
operator's bond.

### 4.2 Epoch Lifecycle

An epoch corresponds to one difficulty adjustment period (~2016 blocks, ~2
weeks), matching the natural settlement point described in
[Pool Transactions and Derivative Instruments](braidpool_spec.md#pool-transactions-and-derivative-instruments).

1. **Setup phase** (incremental, throughout epoch): As each coinbase matures
   (height + 100), the current SC pre-signs it into the BitVM2 settlement
   template (KickOff, Assert, Disprove, and Recovery paths). Pre-signing is
   incremental — each coinbase is signed independently as it becomes eligible,
   rather than requiring a single ceremony at epoch start. If the SC
   composition changes mid-epoch (new block winners rotate into the committee),
   later coinbases are pre-signed under the updated SC.

2. **Mining phase**: Miners produce shares. Share transfers to risk-takers are
   recorded in the braid consensus. Coinbase UTXOs accumulate as standard P2TR
   outputs.

3. **Settlement phase** (epoch end): Each operator (risk-taker) computes the
   UHPO distribution for the completed epoch, pays their miners, and publishes
   a batch settlement claim on-chain. Multiple operators settle in parallel
   (see [Section 6](#6-parallel-batched-settlement)).

4. **Dispute phase**: A challenge window of $D$ blocks during which any
   challenger can submit a fraud proof. We require:
   $$D \geq T_{\text{sync}} + T_{\text{proof}} + T_{\text{confirm}}$$
   where $T_{\text{sync}}$ is the time for a challenger to sync the full DAG
   state, $T_{\text{proof}}$ is the time to generate a SNARK proof and submit
   on-chain fraud proof transactions, and $T_{\text{confirm}}$ is the number
   of confirmations needed for the fraud proof transactions. A conservative
   initial value is $D = 2016$ blocks (~2 weeks), matching the difficulty
   adjustment period. See [Section 4.5](#45-proving-infrastructure) for
   concrete proving time benchmarks.

5. **Finalization**: If no valid fraud proof is submitted, the operator is
   reimbursed from the epoch's coinbase outputs. If a fraud proof succeeds,
   the claim is rejected, the operator's bond is awarded to the challenger,
   and the coinbase funds are returned to the pool.

### 4.2.1 Coinbase Pre-signing Protocol

Under Direct Coinbase Settlement, each block's coinbase output is a standard
P2TR UTXO controlled by the SC active at the time the block is mined. The
pre-signing protocol operates incrementally:

1. **Maturity wait.** A coinbase output becomes spendable at height + 100
   (Bitcoin's coinbase maturity rule). Pre-signing cannot begin until this
   height is reached.

2. **SC identification.** The SC for a given coinbase is the set of $S$
   unique hashers who won the most recent blocks at the time the coinbase
   matures. If the pool has mined additional blocks since the coinbase was
   created, the SC may have rotated.

3. **Template construction.** For each mature coinbase, the current SC
   constructs and pre-signs the BitVM2 transaction templates (KickOff, Assert,
   Disprove, Recovery). Coinbase spending signatures use
   `SIGHASH_ANYONECANPAY | SIGHASH_NONE`, committing only to the individual
   input — not to other inputs or outputs. This decouples pre-signing from
   the settlement structure: the SC does not need to know which operator will
   claim a coinbase, how many batches the settlement will be split into, or
   what the outputs will be. Output correctness is enforced by the BitVM2
   connector, not by the coinbase signatures (see
   [Section 4.3.2](#432-batched-settlement)).

4. **Key management across epoch.** Because the SC rotates as new blocks are
   won, different coinbases within the same epoch may be pre-signed under
   different SC compositions. The `SIGHASH_ANYONECANPAY` flag means each
   coinbase carries a self-contained spending authorization that is valid in
   any settlement transaction, regardless of which other coinbases are
   included.

5. **Failure handling.** If the SC fails to pre-sign a particular coinbase
   (e.g., insufficient signers are online), that coinbase is excluded from the
   current epoch's settlement. It rolls to the next epoch, where a new SC
   attempt is made. This per-coinbase failure isolation is a key advantage
   over aggregated models where a single signing failure blocks the entire
   epoch. If a coinbase remains unsettled for more than 2 epochs (failure to
   pre-sign persists across SC rotations), it falls back to FROST signing with
   the current SC, using the same mechanism as
   [Section 7](#7-bootstrapping-and-fallback). This prevents indefinite
   accumulation of stuck coinbases.

### 4.3 Transaction Structure

BitVM2 uses pre-signed transaction graphs with *connector outputs* — one-time
spending gates that create mutually exclusive execution paths. When one path
consumes a connector output, all alternative paths become unspendable, enforcing
mutual exclusivity without requiring new signatures.

In Braidpool's Direct Coinbase Settlement, the individual coinbase UTXOs serve
as the locked funds (analogous to the "peg-in" UTXOs in generic BitVM2
bridges). There is no separate peg-out step — the coinbases *are* the UTXOs
being settled. This is a key simplification compared to generic BitVM2 bridges:
the pool's coinbase rewards are already locked as standard P2TR outputs, so
the "deposit" phase is implicit in the mining process itself. Each coinbase
remains as an individual UTXO controlled by the SC active when the block was
mined.

The SC incrementally pre-signs settlement templates as coinbases mature
(height + 100), using `SIGHASH_ANYONECANPAY | SIGHASH_NONE` so that each
coinbase's spending authorization is independent of the settlement structure.
At epoch end, each operator constructs a *batch* settlement transaction
spending a subset of pre-signed coinbases (see
[Section 4.3.2](#432-batched-settlement)). Three paths are possible per batch:

```
Shared layer (one per epoch):
  KickOff1 (operator commits UHPO Merkle root)
      --> KickOff2 (after challenge window)
           --> Assert anchors proven UHPO root on-chain (if disputed)

Per-batch layer (one per operator):
  Happy path:
    [N coinbase inputs] + [batch connector referencing proven UHPO root]
        --> Take1 (operator reimbursed, batch UHPO outputs paid)

  Unhappy path:
    Assert --> Challenge (challenger posts 1 BTC bond)
        --> Disprove (~4 MB, challenger re-executes faulty chunk)
              --> Bond to challenger + coinbases returned to pool

  Timeout path:
    KickOff1 --> KickOff Timeout Tx (handles non-responsive operator)
```

In the happy path, each operator's batch settlement goes unchallenged and
finalizes independently. In the unhappy path, a challenger disputes the shared
UHPO computation or a specific batch's output subset. The connector outputs
ensure that once a challenger initiates a dispute, the operator's claim path
is invalidated.

If a coinbase's SC fails to pre-sign, that coinbase is excluded from the
settlement and rolls to the next epoch. This provides failure isolation: a
single uncooperative SC member cannot block the entire epoch's settlement,
only the specific coinbases they refuse to sign.

The SC does not need to be online during the dispute phase — all paths are
pre-signed during setup. The security model requires only that at least one SC
member honestly deletes their key share after pre-signing (1-of-N honesty
assumption).

### 4.3.1 Multi-Input Settlement Transaction

The settlement transaction at epoch end has the following structure:

**Inputs** (~2016 coinbase UTXOs):
- Each input spends one coinbase P2TR output from the epoch.
- Each input carries a Schnorr signature from the SC that pre-signed it.
- Coinbases whose SC failed to pre-sign are excluded (partial settlement).

**Connector input** (1 UTXO):
- Created by the KickOff transaction as part of the BitVM2 flow.
- Carries the settlement logic (hybrid taproot leaves for covenant/dispute
  paths, see [Section 9.3](#93-critical-analysis)).
- Under a covenant soft fork, this input would enforce output binding via
  OP_COHV or equivalent.

**Outputs** (UHPO distribution):
- One output per miner receiving payment (the UHPO set).
- Operator reimbursement output.
- Bond output (returned to operator after dispute window, or to challenger).

Miners whose UHPO payout falls below Bitcoin's dust threshold (546 satoshis
for P2TR) are excluded from the current epoch's settlement. Their unclaimed
balance accumulates across epochs and is paid out when it exceeds the
threshold. The operator tracks accumulated balances in the off-chain DAG
state.

**Size analysis:**
- ~2016 inputs × ~107 bytes each (41-byte non-witness [36-byte outpoint +
  4-byte sequence + 1-byte scriptSig length] + 66-byte witness [1-byte item
  count + 1-byte length + 64-byte Schnorr signature]) ≈ ~215 KB total input
  data.
- Outputs depend on the number of distinct miners; with batching, typically
  hundreds of outputs ≈ ~15–30 KB.
- Total transaction: ~230–245 KB. Weight (BIP 141) = 4 × non-witness +
  1 × witness. With ~91 KB non-witness and ~133 KB witness: ~498 KWU, well
  within Bitcoin's 4000 KWU block weight limit.

**Fee economics.** A single monolithic settlement (~2016 inputs) weighs ~498
KWU, or ~125 KvB — exceeding Bitcoin Core's 400 KWU standardness limit. Under
batched settlement ([Section 4.3.2](#432-batched-settlement)), each batch of
~500 inputs weighs ~120–180 KWU (~30–45 KvB). At 20 sat/vB, each batch costs
approximately 0.006–0.009 BTC; during fee spikes (100+ sat/vB), ~0.03–0.045
BTC. The total epoch fee across all batches is comparable to the monolithic
case, but each batch is independently standard and relayable. Each operator
bears their batch's fee and is reimbursed from the settlement.

**BitVM2 connectors:** The standard BitVM2 mutual-exclusivity connectors gate
between the happy path (Take1) and unhappy path (Challenge → Assert →
Disprove). These are distinct from the settlement logic connector described
above. The mutual-exclusivity connectors ensure that once a dispute begins,
the operator's happy-path claim is invalidated.

### 4.3.2 Batched Settlement

A single settlement transaction spending ~2016 coinbase inputs weighs ~498
KWU, which exceeds Bitcoin Core's default `MAX_STANDARD_TX_WEIGHT` of 400,000
WU. Non-standard transactions are not relayed by default nodes and must be
submitted directly to a cooperating miner. The batched settlement model
eliminates this constraint by splitting the settlement into multiple smaller
transactions, each well under the standardness limit.

**Architecture.** Because coinbase pre-signatures use
`SIGHASH_ANYONECANPAY | SIGHASH_NONE` (see
[Section 4.2.1](#421-coinbase-pre-signing-protocol), item 3), each coinbase's
spending authorization is independent of the settlement structure. This
enables *late binding*: the allocation of coinbases to operators is determined
at epoch end, not at pre-signing time. Each operator constructs a batch
transaction spending only their allocated coinbases:

```
Operator A (serves miners 1-50, derivative contracts):
  [~600 coinbases] + [batch connector A] → miners 1-50 payouts + A's reimbursement

Operator B (serves miners 51-120, derivative contracts):
  [~800 coinbases] + [batch connector B] → miners 51-120 payouts + B's reimbursement

Operator C (non-derivative miners 121-200):
  [~616 coinbases] + [batch connector C] → miners 121-200 payouts + C's reimbursement
```

Each batch transaction weighs ~120–180 KWU, comfortably under the 400 KWU
standardness limit. All batches can be submitted and finalize in parallel.

**Coinbase allocation protocol.** At epoch end, operators announce their miner
sets (known from derivative contracts recorded in the braid consensus). The
epoch's coinbase UTXOs are allocated proportionally: each operator receives
coinbases whose total value covers their miners' payouts plus reimbursement.
Bitcoin's UTXO model provides double-spend protection — once a coinbase is
confirmed in one batch, it cannot appear in another.

**Shared UHPO proof, per-batch connectors.** The UHPO computation (cohort
identification, share formula, per-miner aggregation) is the same regardless
of batching. A single SNARK proof covers the entire epoch's distribution,
anchoring a Merkle root of all miner payouts. Each batch connector carries a
Merkle inclusion proof showing that the batch's output subset is valid against
the proven root. A challenger can dispute at either layer:

- **Computation dispute:** The UHPO SNARK is incorrect. Standard BitVM2
  Assert/Disprove against the shared proof.
- **Subset dispute:** A batch's outputs don't match the proven distribution.
  Merkle subset fraud proof against the batch connector — much simpler and
  cheaper than a full SNARK dispute.

**Partitioning fraud proof.** The operator commits to a partition (which
miners and coinbases belong to each batch) in the KickOff transaction. The
SNARK circuit additionally proves partition consistency: every coinbase
appears in exactly one batch, every miner appears in exactly one batch, and
each batch's coinbase total covers its output total. Alternatively, a
separate lightweight fraud proof verifies partition consistency without
modifying the UHPO SNARK.

**Relationship to parallel settlement.** Batched settlement is the
architecture underlying
[Section 6](#6-parallel-batched-settlement): each risk-taker settles their
own miners in a separate batch. A single operator claiming all batches is a
special case. See Section 6 for the full epoch-end protocol.

### 4.4 Fraud Proof Specification

We define three types of fraud:

**Type A: Wrong DAG state.** The operator commits to a Merkle root of the DAG
state. Each Bitcoin block's coinbase OP_RETURN already includes the braid DAG
state Merkle root (see
[Metadata Commitments](braidpool_spec.md#metadata-commitments)). A challenger
can prove that the operator's committed Merkle root contradicts the OP_RETURN
commitments anchored in Bitcoin's proof of work.

**Type B: Wrong computation.** The operator's proposed UHPO distribution does
not match the result of applying the share formula to the committed DAG state.
The computation includes:

- Cohort identification from the DAG structure,
- Per-share value computation using the formula $s = 1/(x \cdot (1 - P_{\geq 2}))$,
- Per-miner aggregation across all shares in the epoch.

**Type C: Operator didn't pay.** The operator claims to have paid miners but
the payments are incorrect or absent. See [Section 4.7](#47-proof-of-payment)
for the verification mechanism.

The fraud proof uses BitVM2 SNARK verification, not the multi-round bisection
protocol of BitVM1. The process is:

1. **Off-chain proving.** The UHPO computation is compiled to a RISC-V program
   and executed in a zkVM. The prover generates a STARK proof of correct
   execution, then wraps it in a Groth16 SNARK for on-chain verification.

2. **On-chain verification.** The Groth16 verifier (~1.2 GB total script) is
   split into approximately 611 chunks, each ≤4 MB to fit in a single Bitcoin
   block. Winternitz One-Time Signatures (WOTS) provide bit-commitments between
   chunks, binding the intermediate values across transactions.

3. **Dispute protocol.** This is a single-round challenge, not a multi-round
   bisection:
   - The operator commits to the output state in the KickOff transaction.
   - If challenged, the operator reveals all intermediate values $z_1 \ldots
     z_{42}$ in the Assert transaction (~4.8 MB).
   - The challenger identifies a faulty chunk $f_i$ where $f_i(z_{i-1}) \neq
     z_i$ and re-executes it on-chain in the Disprove transaction (~4 MB).
   - Maximum dispute length: 2 rounds (4 transactions).

The UHPO computation is estimated at approximately $2 \times 10^6$ steps:

| Component | Estimated Steps |
| --------- | --------------- |
| Cohort identification (DAG traversal) | ~500K |
| Share formula evaluation per share | ~10 ops × ~100K shares = ~1M |
| Per-miner aggregation | ~100K |
| Merkle proof verification | ~300K |

These $\sim 2 \times 10^6$ steps are compiled to a RISC-V program and proven
via STARK, then verified on-chain via Groth16 SNARK. The step count determines
the prover's workload (and thus the proving time in
[Section 4.5](#45-proving-infrastructure)), not the number of on-chain dispute
rounds.

### 4.5 Proving Infrastructure

The off-chain SNARK proof pipeline requires selecting a zkVM and provisioning
proving hardware.

**zkVM selection.** The two leading candidates are
[RISC Zero](https://www.risczero.com/) (used by Citrea's Clementine bridge)
and [SP1](https://succinct.xyz/) (Succinct Labs). Both compile Rust programs
to RISC-V and generate STARK proofs that can be wrapped in Groth16 SNARKs for
Bitcoin verification. RISC Zero has the most BitVM2 deployment experience
through Citrea; SP1 offers competitive proving times. The choice depends on
toolchain maturity at implementation time.

**Proving time estimates.** Benchmarks from GOAT Network's testnet and Alpen
Labs provide concrete performance data. Each figure below measures a different
component of the proving pipeline:

| Component | Hardware | Time | Source |
| --------- | -------- | ---- | ------ |
| Groth16 SNARK proof | GOAT testnet GPU | ~10.4 s | GOAT Network |
| Block proof generation | GOAT testnet | ~2.6 s | GOAT Network |
| Proof aggregation | GOAT testnet | ~2.7 s | GOAT Network |
| End-to-end pipeline | GOAT testnet (optimized) | ~15.7 s total | GOAT Network |
| Consumer CPU (Groth16) | General estimate | ~3–6 minutes | Alpen Labs |

The end-to-end pipeline time (~15.7 s) is the sum of individual components
(Groth16 proof + block proof + aggregation), not a separate measurement.

**Hardware implications.** Operators need GPU hardware (commodity gaming GPUs
suffice) for timely proving. Consumer-grade CPUs can generate proofs but
require minutes rather than seconds, which may be acceptable for Braidpool's
settlement cadence (epoch-level, not per-block). Specialized ASIC-class
infrastructure is not required.

### 4.6 On-Chain State Commitments

Each Bitcoin block's coinbase OP_RETURN includes a hash of the serialized
`BraidpoolMetadata` struct, which contains:

- `parents`: the bead's parent hashes and timestamps,
- `payout_address`: the miner's P2TR payout address,
- `comm_pubkey`: secp256k1 key for encrypted communication.

These commitments anchor the off-chain DAG state to Bitcoin's proof of work,
making it available for fraud proof verification. An operator cannot falsify the
DAG state without also falsifying Bitcoin blocks.

### 4.7 Proof of Payment

When claiming reimbursement, the operator must demonstrate that miners were
actually paid the correct amounts. This is the *execution fidelity* problem:
even if the computation is correct, the operator might not execute the payments.

The operator publishes a claim containing:

1. The UHPO distribution Merkle root (what should be paid),
2. A list of payment transaction IDs (what was paid).

We consider three approaches to verifying payment execution:

**Approach 1: SPV proof in BitVM circuit.** The challenger provides a Bitcoin
block header and Merkle inclusion proof demonstrating that a claimed payment
txid either does not exist in the specified block or has incorrect
amounts/destinations. This is the most trust-minimized approach — it requires
only Bitcoin's existing SPV security model. The cost is additional circuit
complexity: each SPV proof verification adds approximately 500K computation
steps to the fraud proof circuit.

**Approach 2: SC escrow verification.** Before releasing the timelocked output,
SC members independently verify that the operator's payment transactions exist
on-chain with correct amounts and destinations. Only after $\lceil 2S/3 \rceil
+ 1$ SC members attest to payment correctness does the timelocked output become
spendable. This approach closes the output-binding gap (see
[Section 5.2](#52-the-output-binding-gap)) but re-introduces an SC liveness
requirement during the finalization phase.

**Approach 3: Extended monitoring period.** The operator claims reimbursement
after an extended timeout (e.g., $2D$ blocks). During this period, any node can
verify payments and raise an alarm via the social layer (e.g., alerting other
miners to withhold future cooperation). This provides the weakest on-chain
guarantees but is the simplest to implement.

**Recommendation:** Approach 1 (SPV proof) as the primary mechanism, with
Approach 2 (SC escrow) as a fallback during the bootstrapping phase when the
BitVM circuit has not yet been fully implemented and audited.

### 4.8 Bond Sizing

The operator's bond must be large enough that the expected profit from fraud is
negative. We require:

$$B \geq \max\left(\pi_{\text{fraud}},\; C_{\text{challenge}}\right)$$

where $\pi_{\text{fraud}}$ is the maximum profit from submitting an incorrect
settlement, and $C_{\text{challenge}}$ is the cost for a challenger to generate
and submit a fraud proof (ensuring challengers are always incentivized).

In practice, the fraud profit is bounded by the total epoch coinbase value
$V_{\text{epoch}} = \sum_i v_i$ where $v_i$ is the value of each included
coinbase. We parameterize the bond as:

$$B = \alpha \cdot V_{\text{epoch}}, \qquad \alpha \in [0.1, 1.0]$$

- $\alpha = 1.0$ provides full security against the output-binding gap: the
  operator risks losing their entire bond (equal to the epoch's coinbase
  value) if they misbehave.
- $\alpha = 0.5$ is a practical starting point: the operator risks losing half
  the epoch's value, which already exceeds any rational fraud profit when
  accounting for reputational damage and loss of future operating income.
- $\alpha < 0.1$ is insufficient because challenger costs could exceed the
  bond, removing the incentive to challenge. The Babylon mainnet test (June
  2025) measured full unhappy-path fees at approximately 14.88M sat (~$16K at
  then-current rates), with the challenger bearing the Disprove transaction
  cost (~10.99M sat, ~$12K) and the operator bearing the Assert cost (~3.89M
  sat, ~$4K). The bond must exceed the *challenger's* costs to maintain
  incentive compatibility — if the bond is less than the Disprove cost,
  rational challengers will not dispute even fraudulent claims.

The bond is returned to the operator upon successful finalization (after the
dispute window with no valid fraud proof).

**Capital requirements.** For a pool with fraction $p$ of network hashrate,
$V_{\text{epoch}} \approx p \times 2016 \times 3.125$ BTC (post-2024 halving).
At $\alpha = 0.5$: a 1% pool requires ~31.5 BTC bond (~$3M), a 5% pool
requires ~157 BTC (~$15M). This concentrates the operator role among
well-capitalized entities, which is acceptable given that risk-takers are
already well-capitalized by definition
([Section 3.1](#31-the-derivatives-market)). However, it constrains the number
of potential operators and should be considered when calibrating $\alpha$.

### 4.9 Deployment Validation

BitVM2 has been validated in production by multiple independent projects:

| Project | Status | Date | Details |
| ------- | ------ | ---- | ------- |
| Babylon (Fairgate) | Full unhappy-path test | June 2025 | 42 blocks (~7.5 hours), ~$16K in fees. First complete dispute resolution on mainnet. |
| Bitlayer | Mainnet bridge | July 2025 | First functional BitVM bridge deployment. |
| Citrea (Clementine) | Mainnet bridge | January 2026 | BitVM2-based, RISC Zero prover, audited. |
| GOAT Network | Testnet | August 2025 | Real-time proving with Groth16 SNARK in ~10.4 s on GPU. |

These deployments confirm that the BitVM2 dispute mechanism works end-to-end
on Bitcoin mainnet. The Babylon test is particularly relevant: it exercised the
full unhappy path (KickOff → Challenge → Assert → Disprove) and validated the
fee estimates used in [Section 4.8](#48-bond-sizing). No BitVM2-specific
security incidents have been reported as of February 2026, though deployments
remain early-stage with limited total value locked.

## 5. Security Analysis

### 5.1 Trust Assumptions

We enumerate all trust assumptions required by this proposal:

1. **SC honest majority.** At least $\lceil 2S/3 \rceil + 1$ of the $S$ SC
   members are honest and correctly pre-sign the BitVM templates. This is
   inherited from the FROST approach. **Note:** OP_CCV
   ([Section 9.3](#93-critical-analysis)) eliminates this assumption entirely
   by replacing SC-controlled key paths with NUMS-key coinbases whose spending
   rules are enforced by an on-chain covenant state machine.

2. **At least one honest challenger.** During the dispute window, at least one
   party must be online, have the full DAG state, and be willing to submit a
   fraud proof if the settlement is incorrect.

3. **Operator solvency.** The operator must have sufficient capital to front
   payouts to all miners and to post the bond.

4. **Bitcoin censorship resistance.** Fraud proof transactions must be able to
   reach the Bitcoin blockchain within the dispute window. A miner with
   sufficient hashrate to censor specific transactions could prevent fraud proofs
   from being confirmed.

5. **Fraud proof circuit correctness.** The BitVM circuit encoding the UHPO
   computation must be correct. This is a software correctness assumption,
   mitigated by open-source code and public auditing.

6. **Verifier's dilemma.** The 1-of-N honest challenger assumption (item 2)
   has been formally shown to be incentive-incompatible
   ([Lazar et al., 2023](https://arxiv.org/abs/2312.01549)). If the operator
   behaves honestly, challengers earn zero reward, so rational challengers stop
   monitoring, at which point the operator can begin cheating. The "Hollow
   Victory" attack
   ([Yousaf et al., 2025](https://arxiv.org/abs/2504.05094)) further shows
   that challengers may not profit even when they win disputes, due to
   front-running and gas costs.

   Mitigations:
   - **(a) Randomized attention tests.** Periodic forced challenges with
     subsidized rewards ensure that monitoring remains profitable on average.
   - **(b) Monitoring bounties.** A small fee deducted from each epoch's
     settlement funds a bounty pool for active challengers.
   - **(c) Braidpool's structural advantage.** Every Braidpool full node
     already maintains the complete DAG state. The marginal cost of detecting
     Type A fraud (wrong DAG state) and Type B fraud (wrong computation) is
     near-zero — nodes need only re-run the UHPO computation against state
     they already have. However, Type C fraud detection (operator didn't pay)
     requires monitoring Bitcoin on-chain payments, which is additional work
     beyond DAG maintenance.

   This remains an open problem for all optimistic verification systems,
   including both BitVM2 and MATT-based approaches.

### 5.2 The Output-Binding Gap

This is the critical limitation of the proposal and must be clearly understood.

After the dispute window expires, the operator controls the timelocked outputs
(the individual coinbase UTXOs included in the settlement) and can sign *any*
spending transaction. The fraud proof system guarantees that the operator's
*proposed computation* is correct (the right amounts are attributed to the
right miners), but it cannot guarantee that the operator actually *executes*
those payments.

In other words: we can verify that the operator computed the right answer, but
we cannot force the operator to act on it (without covenant opcodes).

**Mitigations:**

- **Bond forfeiture.** If the operator fails to pay, challengers can submit
  proof of non-payment (see [Section 4.7](#47-proof-of-payment)), causing the
  operator to lose their bond.
- **Reputation loss.** An operator who defrauds miners will be excluded from
  future epochs.
- **Repeat-player dynamics.** The present value of future operating fees exceeds
  any single-epoch fraud profit for rational operators.
- **Future covenant soft fork.** Opcodes enabling *output introspection at
  spending time* (e.g., OP_CAT + OP_SHA256, or dedicated introspection opcodes)
  would allow Script to verify that a spending transaction's outputs match a
  dynamically-provided template verified by the fraud proof. See
  [Section 9](#9-covenant-soft-fork-analysis) for a detailed analysis of
  current proposals. Note that OP_CTV alone is insufficient: it commits to a
  fixed template at UTXO creation time, but the UHPO distribution is unknown
  until the epoch ends (Section 2.2). What is needed is the ability to accept a
  template *as witness data* and verify it against the transaction's actual
  outputs.

**Severity: CRITICAL.** This is an acknowledged limitation, not a solved
problem. The proposal is that economic incentives make exploitation irrational
for repeat players, while a future soft fork could provide cryptographic
guarantees.

### 5.3 Security Model

| Guarantee Type | Properties |
| -------------- | ---------- |
| Cryptographic | SC pre-signatures valid, fraud proof circuit correct, DAG state tamper-proof (anchored in Bitcoin PoW) |
| Economic | Bond disincentivizes false claims, challenger bounty incentivizes monitoring, competition among operators reduces rents |
| Trusted | SC honest majority (eliminated by OP_CCV; see [Section 9.3](#93-critical-analysis)), operator execution fidelity (mitigated by bond), challenger availability |

### 5.4 Attack Vectors

| Attack | Mitigation | Severity |
| ------ | ---------- | -------- |
| Operator claims incorrect distribution | Type B fraud proof catches and rejects | Medium |
| Output-binding gap exploitation | Economic: bond forfeiture, reputation, repeat-player dynamics | **Critical** |
| SC + operator collusion | Same severity as FROST 67% attack (SC threshold is $\lceil 2S/3 \rceil + 1$) — inherited, not new. **Eliminated by OP_CCV** (NUMS key path, covenant-enforced settlement; see [Section 9.3](#93-critical-analysis)) | **Critical** (without covenants) / Eliminated (with OP_CCV) |
| No honest challenger available | Settlement delayed; bond covers costs if eventually challenged. See verifier's dilemma ([Section 5.1](#51-trust-assumptions), item 6) | High |
| Grief attack (frivolous challenges) | Challenger must post 1 BTC bond and execute full on-chain dispute — bond forfeiture makes griefing expensive | Low |
| Dispute window timing manipulation | Use block height, not wall-clock timestamps | Medium |
| Partial SC failure (some coinbases not pre-signed) | Exclude unsigned coinbases from settlement; they roll to next epoch. Partial settlement proceeds with remaining coinbases | Low |

### 5.5 Comparison with FROST-Only Approach

| Property | FROST-Only | BitVM + Risk-Taker |
| -------- | ---------- | ------------------ |
| Liveness failures | All signers must complete signing | Only operator + 1 challenger needed |
| Nonce generation | Interactive, failure-intolerant | Not required |
| Signing complexity | $O(S^2)$ communication rounds | Pre-signed templates, no interaction |
| Output-binding gap | None (signers directly produce tx) | **New limitation** |
| Challenger requirement | None | At least one honest challenger |
| Capital requirement | Minimal | Operator must front payouts + bond |
| Per-block FROST signing | Yes (~2016/epoch) | No (incremental pre-signing only) |
| SC key deletion | Required, unverifiable | Required for template pre-signing |
| SC collusion risk | Same | Same (inherited) |
| Failure isolation | None (all-or-nothing) | Per-batch (parallel settlement, partial OK) |
| Bootstrapping | Works from block 5 | Requires derivatives market |

## 6. Parallel Batched Settlement

The batched settlement architecture
([Section 4.3.2](#432-batched-settlement)) combines naturally with the
risk-taker model: each risk-taker settles their own miners in a separate
batch transaction, in parallel.

### 6.1 Epoch-End Settlement Protocol

1. **UHPO computation.** The epoch ends. Every Braidpool full node computes
   the UHPO distribution from the finalized DAG state.

2. **Operator announcement.** Each risk-taker announces their claim: which
   miners they serve (known from derivative contracts recorded in the braid
   consensus) and which coinbase UTXOs they request. Announcements are
   broadcast via the Braidpool P2P network.

3. **Coinbase allocation.** Coinbase UTXOs are allocated to operators
   proportionally — each operator receives coinbases whose total value covers
   their miners' payouts plus their reimbursement. Allocation follows a
   deterministic rule (e.g., coinbases assigned in block-height order to
   operators in order of announcement) so all nodes agree on the partition
   without coordination.

4. **Non-derivative miners.** Miners who did not engage a risk-taker are
   assigned to the first operator willing to include them, or to a dedicated
   "residual" operator. The residual operator's incentive is the processing
   fee deducted from non-derivative miners' payouts.

5. **Batch submission.** Each operator constructs and submits their batch
   transaction independently. All batches share a single UHPO SNARK proof;
   each batch connector carries a Merkle inclusion proof for its output
   subset.

6. **Parallel dispute windows.** Each batch enters its own dispute window.
   A dispute on batch A does not affect batch B's finalization. Challengers
   can target specific batches independently.

7. **Finalization.** Each batch finalizes independently after its dispute
   window expires without a valid fraud proof. The operator is reimbursed,
   the bond is returned, and the batch's miners receive their payouts.

### 6.2 Bond Structure

Each operator posts a bond proportional to their batch's value:
$B_i = \alpha \cdot V_i$ where $V_i$ is the total coinbase value in batch
$i$. This is more capital-efficient than a single operator bonding the
entire epoch: each risk-taker bonds only the portion they settle.
A challenger who successfully disputes batch $i$ receives $B_i$.

### 6.3 Failure Modes

**Operator fails to submit batch.** If an operator does not submit their
batch within $F = 144$ blocks after the epoch ends, their allocated coinbases
are released and can be claimed by another operator or fall back to FROST
signing ([Section 7](#7-bootstrapping-and-fallback)).

**Disputed batch.** If a batch is successfully disputed, the operator's bond
is forfeited, and the batch's coinbase UTXOs remain under SC control. A new
operator can claim those coinbases, or they fall back to FROST.

**Partial epoch settlement.** Some batches may finalize while others are
disputed or abandoned. Miners in finalized batches receive their payouts
regardless of what happens to other batches. This extends per-coinbase
failure isolation to per-batch failure isolation.

### 6.4 Special Cases

**Single operator.** If only one risk-taker is active (e.g., during early
pool growth), they claim all coinbases in a single batch — or split into
multiple batches to stay under the standardness limit. The protocol degrades
gracefully to the single-processor model.

**No operators.** If no risk-taker announces a claim, the epoch falls back
to FROST signing ([Section 7](#7-bootstrapping-and-fallback)).

**Competitive pressure.** Risk-takers compete for miners by offering lower
fees and better service. Miners can switch risk-takers between epochs. This
permissionless competition prevents rent extraction.

## 7. Bootstrapping and Fallback

The BitVM settlement mechanism requires an active derivatives market with
risk-takers willing to act as operators. During the pool's early stages, this
market may not exist.

**First 4 blocks.** Direct payout to hashers. There are not enough known
parties to construct a threshold signature (see
[Payout Authorization](braidpool_spec.md#payout-authorization)).

**Early pool (few miners, no risk-takers).** FROST/ROAST threshold signing on
individual coinbase UTXOs is the primary mechanism. Each coinbase is a standard
P2TR output controlled by the SC, and the SC directly signs the UHPO payout
transaction — the same coinbase format used under Direct Coinbase Settlement,
but without the BitVM2 dispute layer.

**Transition.** As the derivatives market develops and risk-takers begin
operating, the BitVM settlement model becomes available. Both mechanisms can
coexist: some epochs may use FROST, others may use BitVM settlement. The
coinbase format (standard P2TR) remains the same in both cases.

**Fallback.** If no operator proposes a settlement within $F = 144$ blocks (~1
day) after an epoch ends, the pool reverts to FROST signing for that epoch. The
FROST signing uses the same SC: the unique hashers who won the most recent $S
\approx 50$ blocks. This ensures liveness even when no risk-taker is available,
at the cost of the known FROST limitations (liveness, 51% attack risk).

**Multi-epoch overlap.** Epoch N's settlement occurs while epoch N+1 is being
mined. If epoch N's fraud proof succeeds (operator's claim rejected), the
epoch's coinbase UTXOs remain under SC control and are available for a new
operator's claim or FROST fallback. The $F = 144$ block timeout restarts.
Epoch N+1's settlement is independent — its operator claims reimbursement from
epoch N+1's coinbases, not epoch N's. No cross-epoch dependency exists: each
epoch's coinbase pool is a disjoint set of UTXOs.

## 8. Open Problems

Several aspects of this proposal require further research:

1. **Dispute window calibration.** The inequality $D \geq T_{\text{sync}} +
   T_{\text{proof}} + T_{\text{confirm}}$ gives a lower bound, but the actual
   values of these components depend on network conditions and proving
   infrastructure. The benchmarks in [Section 4.5](#45-proving-infrastructure)
   provide initial estimates; validation against Braidpool's specific UHPO
   computation on representative hardware is needed.

2. **Bond sizing dynamics.** The parameter $\alpha$ may need to be adjusted
   dynamically based on the number of miners, the total epoch coinbase value, and observed
   challenger behavior. A fixed $\alpha$ may be too conservative (locking up
   unnecessary capital) or too aggressive.

3. **Fraud proof circuit implementation.** The UHPO computation (cohort
   identification, share formula, per-miner aggregation) must be encoded as a
   zkVM program and compiled to a SNARK. The estimated $\sim 2 \times 10^6$
   steps needs validation against an actual implementation.

4. **Covenant alternatives.** Closing the output-binding gap requires opcodes
   that enable *dynamic output introspection*: Script must be able to verify at
   spending time that a transaction's outputs match a template provided as
   witness data. See [Section 9](#9-covenant-soft-fork-analysis) for a detailed
   analysis of current proposals and their applicability to Braidpool.

5. **Economic model validation.** A game-theoretic analysis of the equilibrium
   behavior of operators, challengers, and miners under various parameter
   settings ($\alpha$, $D$, $F$) would strengthen confidence in the proposal's
   security properties.

6. **Challenger incentive sufficiency.** Whether the bond-as-bounty model
   provides sufficient incentive for challengers to monitor settlements needs
   empirical study. If the bond is split among multiple simultaneous
   challengers, each individual challenger's expected reward decreases, which
   may reduce monitoring incentives. The initial proposal awards the full bond to
   the first valid challenger. See also the verifier's dilemma discussion in
   [Section 5.1](#51-trust-assumptions), item 6.

7. **Groth16 trusted setup and the path to transparent proofs.** BitVM2's
   on-chain SNARK verification uses Groth16, which requires a structured
   reference string (SRS) from a trusted setup ceremony. The trusted setup is
   not inherent to BitVM2's architecture — it is an artifact of Groth16 being
   the most efficient proof system whose verification can currently be
   performed in Bitcoin Script without new opcodes. Citrea's Clementine bridge
   already uses Groth16 in production (mainnet January 2026), providing
   practical precedent.

   **Near-term options (no soft fork):**
   - (a) Reuse an existing Groth16 ceremony (Zcash Powers of Tau with 87+
     participants, Hermez, or whatever Citrea adopted). Trust assumption:
     at least one participant destroyed their toxic waste.
   - (b) Run a pool-specific ceremony with open participation.
   - (c) Switch to PLONK with KZG commitments (universal, updateable SRS —
     no per-circuit ceremony, participants can add entropy indefinitely).
     Cost: ~3× larger proofs, but strictly weaker trust assumption.
   - (d) Adopt [Glock](https://eprint.iacr.org/2025/1485) (see Open Problem
     8), which uses a designated-verifier SNARK. **Important clarification:**
     DV-SNARKs are *not* setup-free — the verifier generates a secret
     verification key, and the toxic waste problem persists. However, in
     BitVM2's challenge-response model the challenger *is* the designated
     verifier, so the setup is per-challenger rather than a shared ceremony.

   **Why transparent (setup-free) alternatives fail without OP_CAT.** The
   constraint is that verification must execute in Bitcoin Script, which has no
   loops and limited stack depth. Pairing-based verification (Groth16, PLONK)
   is compact: 3 pairings, constant time. All known transparent proof systems
   either have verification too expensive for Script, or require OP_CAT:

   - *STARKs* (hash-based, quantum-resistant): verification is
     $O(\log^2 n)$ hash operations — efficient enough for Script, but Merkle
     proof verification requires concatenating siblings before hashing, which
     needs OP_CAT. This is the *only* transparent system with a demonstrated
     Bitcoin Script verifier (see [Section 9.3](#93-critical-analysis)).
   - *Bulletproofs* (discrete-log-based, no trusted setup): verification
     requires a multi-scalar multiplication $\sum_{i=1}^{n} s_i \cdot G_i$
     over $n$ generator points, where $n$ is the circuit size. This is
     $O(n)$ group operations — *linear* in the circuit. For Braidpool's
     UHPO circuit ($n \sim 10^6$), this means ~$10^6$ elliptic curve
     multiplications. Each EC multiplication in Script requires hundreds of
     opcodes (big-integer modular arithmetic emulated in 4-byte CScriptNum).
     The BitVM2 Assert transaction for Groth16 (3 pairings) is already
     ~4.8 MB; for Bulletproofs it would be on the order of *terabytes* —
     completely infeasible. The linear verifier is fundamental to the IPA
     (Inner Product Argument) construction and cannot be improved without
     changing the proof system.
   - *Halo2 / IPA-based PLONK* (discrete-log, no trusted setup): same
     $O(n)$ verification bottleneck as Bulletproofs. Also not quantum-safe.
   - *Nova / folding schemes* (discrete-log, transparent): efficient for
     incremental computation (the UHPO calculation is naturally incremental),
     but the final proof still requires a base SNARK verifier — deferring
     the setup question to the inner proof system, not eliminating it.
   - *Binius* (binary tower fields, hash-based, quantum-resistant): a
     promising research direction using native binary arithmetic (~5× faster
     than Mersenne-31 for XOR-heavy computations), but no Bitcoin Script
     verifier exists or has been proposed.

   **OP_CAT is the critical dependency.** It unlocks the entire class of
   hash-based transparent proof systems for Bitcoin Script. A single soft fork
   simultaneously solves two of Braidpool's open problems: trustless output
   binding (the sighash reconstruction trick) and elimination of the trusted
   setup (STARK verification). See the Circle STARK discussion in
   [Section 9.3](#93-critical-analysis).

   **Quantum vulnerability.** Groth16's security rests on the hardness of
   the discrete logarithm problem in pairing-friendly elliptic curves —
   broken by Shor's algorithm on a fault-tolerant quantum computer.
   Bulletproofs, Halo2, and Nova share this vulnerability (all discrete-log-
   based). Only hash-based systems (STARKs, Circle STARKs, Binius) are
   quantum-resistant by construction.

8. **BitVM evolution.** BitVM3-RSA
   ([Linus et al., July 2025](https://bitvm.org/bitvm3)) was retracted due
   to a security break discovered by Liam Eagen at Fairgate Labs.
   [Glock](https://eprint.iacr.org/2025/1485) (Garbled Locks, Alpen Labs)
   is the most promising successor, offering up to ~1000× lower on-chain
   costs than BitVM2 for Assert transactions (~56 kB vs. ~4.8 MB). The
   Starknet blog reports ~550× for total on-chain data reduction in their
   specific deployment, which includes overheads beyond Assert alone.

   Glock uses a designated-verifier SNARK (DV-SNARK) based on a modified
   Pari construction. The DV-SNARK replaces expensive pairing verification
   with scalar multiplication, enabling instantiation over any elliptic
   curve (not necessarily pairing-friendly) — Glock uses a binary curve for
   compatibility with garbled circuits. **DV-SNARKs are not setup-free:**
   the verifier generates a secret verification key, and the toxic waste
   problem persists at the per-verifier level. However, in BitVM2's
   challenge-response model, the challenger is the designated verifier and
   generates their own key, so the trust model differs from a shared
   ceremony: each challenger's setup is self-sovereign.

   Glock has progressed from research to active development: the
   [Starknet Foundation](https://www.starknet.io/blog/starknet-alpen-bitcoin-glock/)
   has funded a shared Glock verifier for the Starknet–Bitcoin bridge,
   with a target 2026 deployment. Braidpool should track Glock for future
   adoption while building on the proven BitVM2 architecture. Note that
   Glock does not eliminate the trusted setup problem (see Open Problem 7)
   — only OP_CAT + STARKs achieves that.

9. **Batched settlement details.** The batched settlement model
   ([Section 4.3.2](#432-batched-settlement)) resolves the standardness
   concern (each batch is under 400 KWU) but introduces new questions:
   (a) the deterministic coinbase allocation rule must be specified precisely
   to prevent disagreements between nodes, (b) the partition consistency
   proof (ensuring every coinbase and every miner appears in exactly one
   batch) needs to be designed — either as part of the UHPO SNARK circuit or
   as a separate lightweight fraud proof, and (c) the interaction between
   per-batch dispute windows and the shared UHPO proof needs analysis: if
   the shared proof is disputed, should all batch dispute windows pause?

## 9. Covenant Soft Fork Analysis

The output-binding gap ([Section 5.2](#52-the-output-binding-gap)) is the
critical limitation of this proposal. Covenant opcodes — Script primitives that
constrain *where* funds can be spent, not just *who* can sign — would close
this gap. This section evaluates the current covenant proposals against
Braidpool's specific requirements.

### 9.1 Braidpool's Requirement

Braidpool needs three distinct on-chain capabilities:

1. **Output binding.** At spending time, Script must verify that a
   transaction's outputs match a template provided as witness data. This
   template is the UHPO distribution, which is unknown at UTXO creation time
   (see [Section 2.2](#22-the-unknown-future-problem)). OP_CTV
   ([BIP 119](https://github.com/bitcoin/bips/blob/master/bip-0119.mediawiki))
   alone is insufficient: it commits to a *fixed* template at UTXO creation
   time, but the UHPO distribution is computed *after* the epoch ends. What is
   needed is the ability to accept a template as witness data and verify it
   against the transaction's actual outputs at spending time.

2. **Fraud proof verification.** On-chain execution of SNARK verification
   chunks in the dispute protocol. Currently handled by BitVM2's pre-signed
   transaction graph, but native Script support could reduce the on-chain
   footprint from megabytes to kilobytes.

3. **SC trust elimination.** The ability to enforce correct settlement without
   relying on the SC's honest majority. Under the current design, a miner
   controlling $\geq \lceil 2S/3 \rceil + 1$ of the most recent $S$ blocks can
   populate the SC with Sybil identities and spend coinbases via the taproot
   key path, bypassing BitVM2 entirely ([Section 5.4](#54-attack-vectors)).
   Eliminating the SC trust assumption requires that the coinbase's spending
   rules be enforced by the Script interpreter, not by the SC's willingness to
   sign correctly.

These are *distinct* requirements. A proposal might satisfy one without the
other. Under Direct Coinbase Settlement, requirement 1 applies to the
settlement transaction that spends ~2016 individual coinbase UTXOs: Script on
the connector input must verify that the transaction's outputs (the UHPO
distribution) match the fraud-proof-validated template.

### 9.2 Proposal Assessment

| Proposal | BIP | Output Binding | Fraud Proofs | SC Trust Eliminated | Maturity | Notes |
| -------- | --- | -------------- | ------------ | ------------------- | -------- | ----- |
| OP_CTV | [119](https://github.com/bitcoin/bips/blob/master/bip-0119.mediawiki) | Static only | No | No | Implementation ready | Commits at creation time; Braidpool needs dynamic |
| CTV + CSFS | [119](https://github.com/bitcoin/bips/blob/master/bip-0119.mediawiki) + [348](https://github.com/bitcoin/bips/blob/master/bip-0348.mediawiki) | Delegated (SC signs template) | No | No (SC signs hash) | Implementation ready | Cryptographic output binding, but requires SC liveness |
| OP_CSFS | [348](https://github.com/bitcoin/bips/blob/master/bip-0348.mediawiki) | With OP_CAT | No | No | Implementation ready | Forces tx data onto stack; limited without CAT |
| OP_CAT | [347](https://github.com/bitcoin/bips/blob/master/bip-0347.mediawiki) | Yes (sighash trick) | No | No (fraud proofs still need SC) | Signet since April 2024 | Reconstructs sighash → extracts hashOutputs |
| OP_TXHASH | [346](https://github.com/bitcoin/bips/pull/1500) | Yes | No | No (same as CAT) | Bitcoin Core PR #29050 | TxFieldSelector hashes chosen fields; cleaner than CAT trick |
| OP_CCV (MATT) | [443](https://github.com/bitcoin/bips/pull/1793) | Yes (if included) | Yes | **Yes** (NUMS key, on-chain state machine) | Specification stage, no activation timeline | Merkle tree state machine; replaces BitVM2 (~7,000 vbytes vs. megabytes); eliminates 67% attack |
| LNHANCE | [119](https://github.com/bitcoin/bips/blob/master/bip-0119.mediawiki) + [348](https://github.com/bitcoin/bips/blob/master/bip-0348.mediawiki) + IKEY + [442](https://github.com/bitcoin/bips/pull/1699) | Delegated (CTV + CSFS) | No | No | Bundled proposal, 66+ signatories | Bundles CTV + CSFS + OP_INTERNALKEY + OP_PAIRCOMMIT; most likely activation vehicle |
| OP_PAIRCOMMIT | [442](https://github.com/bitcoin/bips/pull/1699) | No | No | No | Draft BIP | Tagged hash combiner for two stack elements; enables Merkle proof verification without OP_CAT. With OP_CAT, redundant since CAT provides arbitrary concatenation |
| OP_COHV | Thought experiment ([Section 9.5](#95-the-output-binding-impossibility)) | Vacuous without cross-input data | No | No | N/A | Collapses to CSFS or CTV unless combined with cross-input introspection. DCS provides a natural cross-input architecture via connector outputs (see [Section 9.5](#95-the-output-binding-impossibility)), though the "vacuous" assessment is unchanged: OP_COHV *per-coinbase* remains trivially satisfiable. |

### 9.3 Critical Analysis

**CTV + CSFS enables delegated covenants but not trustless settlement.** CTV
commits to a fixed output template at the time the UTXO is created. Braidpool's
UHPO distribution is unknown until the epoch ends — potentially weeks after the
coinbase UTXOs are created. CSFS
([BIP 348](https://github.com/bitcoin/bips/blob/master/bip-0348.mediawiki))
verifies a signature over an arbitrary message on the stack, enabling
*delegated* covenants: the spending script
`<SC_pubkey> OP_CHECKSIGFROMSTACKVERIFY OP_CHECKTEMPLATEVERIFY` accepts a
`<signature> <ctv_hash>` witness at spending time. CSFS verifies the SC signed
the CTV hash; CTV verifies the transaction outputs match that hash. This is a
meaningful improvement over pure FROST: with FROST, the SC signs the spending
*transaction* and can redirect funds to arbitrary outputs; with delegated CTV,
the SC signs a *template hash* and CTV cryptographically enforces the outputs.
The output binding becomes cryptographic rather than purely trust-based.

However, delegated CTV + CSFS still requires the SC to be **online at
settlement time** — someone must compute the correct UHPO distribution, create
the CTV hash, and sign it. This is the same liveness requirement that motivates
the BitVM2 approach in the first place (see
[Section 1](#1-introduction-and-problem-statement)). Furthermore, without
OP_CAT, Script cannot independently verify that the signed CTV hash corresponds
to the *correct* UHPO distribution. The SC's signature attests "these are the
right outputs," but Script has no way to check that claim against the DAG state.
An honest SC signing a correct template provides strong guarantees; a
compromised SC signing an incorrect template is undetectable on-chain.
Note that the 51% attack described in
[Section 1](#1-introduction-and-problem-statement) applies here: an attacker
who controls enough recent block wins to dominate the SC can sign arbitrary CTV
hashes, making delegated CTV + CSFS no stronger than plain FROST against a
colluding SC. The BitVM2 dispute path (Leaf 2 in the hybrid design) is the
mitigation.

**Hybrid taproot design.** Under Direct Coinbase Settlement, each coinbase
remains a standard P2TR output — fund custody is separated from settlement
logic. The hybrid taproot design applies to the **connector UTXO** created in
the KickOff transaction, not to the coinbase scripts themselves. This
connector carries the settlement logic:

```
Connector UTXO taproot leaves:
  Leaf 1: <SC_pubkey> CSFS + CTV   (SC signs template — fast, output-bound)
  Leaf 2: BitVM2 Assert/Disprove   (operator + fraud proof — slow, trustless)
  Leaf 3: Timelock + FROST fallback (emergency — slowest)
```

This is a key architectural insight: DCS **separates fund custody (coinbase
P2TR) from settlement logic (connector + covenant)**. Under the previous
aggregated model, these were conflated in a single UTXO. By separating them,
the coinbase format remains stable across all upgrade paths, and only the
connector's taproot leaves change as new opcodes become available.

Leaf 1 provides the fast happy path: the SC verifies the operator's UHPO
computation, signs the CTV hash, and the settlement transaction executes with
cryptographic output binding across all ~2016 coinbase inputs. If the SC is
unavailable or disagrees with the operator, Leaf 2 provides the BitVM2 fraud
proof path that requires no SC participation beyond the initial template
pre-signing. Leaf 3 is the FROST fallback for when no operator is available.
This layered design uses each mechanism where it is strongest: CTV + CSFS for
the common case with output binding, BitVM2 for the adversarial case without
SC liveness, and FROST for bootstrapping. Note that this "settlement logic
connector" is distinct from the standard BitVM2 mutual-exclusivity connectors
that gate between execution paths — it carries validated computation results
to constrain settlement outputs.

**OP_CAT closes the output-binding gap.** Using a technique described by
[Poelstra](https://medium.com/blockstream/cat-and-schnorr-tricks-i-faf1b59bd298),
the spender provides sighash preimage components as witness elements; Script
concatenates them with OP_CAT and uses OP_CHECKSIG as a "sighash oracle" to
verify the reconstruction is genuine. Individual components — including
`hashOutputs` — can then be inspected on the stack to verify transaction
outputs match an expected hash. This enables dynamic output
verification at spending time — exactly what Braidpool needs. OP_CAT is the
most mature candidate (active on signet since April 2024, vault prototypes
exist). Note that OP_TXHASH
([BIP 346](https://github.com/bitcoin/bips/pull/1500)) achieves similar output
introspection via a `TxFieldSelector` byte, with cleaner semantics but less
deployment maturity.

**OP_CCV closes the fraud proof gap *and* eliminates the SC trust assumption.**
MATT / OP_CHECKCONTRACTVERIFY
([BIP 443](https://github.com/bitcoin/bips/pull/1793)) enables on-chain state
machines via Merkle tree commitments. For Braidpool, this could replace the
entire BitVM2 pre-signed transaction graph with a native Script-based fraud
proof at approximately 7,000 vbytes — three orders of magnitude smaller than
the current BitVM2 Assert transaction (~4.8 MB). OP_CCV's role is *distinct*
from OP_CAT's: CAT solves output binding, CCV solves on-chain fraud proof
verification. Both would be needed for the most efficient design.

**OP_CCV uniquely eliminates the 67% SC attack.** With OP_CCV, coinbase outputs
can use a NUMS (Nothing-Up-My-Sleeve) internal key — a provably unspendable
taproot key path — so that *all* spending must go through Script leaves
containing the covenant-enforced dispute mechanism. This eliminates the attack
described in [Section 9.1](#91-braidpools-requirement) (requirement 3): even a
miner controlling $\geq 67\%$ of the pool's hashrate cannot steal funds,
because there is no key path to exploit. The spending rules are enforced by the
Script interpreter, not by the SC's willingness to sign correctly.

Critically, this defense does not require the attacker to run honest software
voluntarily — it follows from the braid consensus rules themselves. The
coinbase format (including the OP_CCV covenant) is part of the share validation
rules. A miner running standard Braidpool software produces OP_CCV-locked
coinbases; a miner running forked software that omits the covenant produces
*invalid shares* that honest nodes reject regardless of the attacker's
hashrate. Therefore: (a) a 67% miner running standard software creates
covenant-locked coinbases and cannot steal, (b) a 67% miner running forked
software cannot get invalid shares accepted into the DAG. The SC trust
assumption is eliminated entirely.

No other covenant proposal achieves this. CTV + CSFS delegates output binding
to the SC, preserving the trust assumption. OP_CAT enables trustless output
binding (via sighash reconstruction) but does not natively support the on-chain
state machine needed to embed the full dispute mechanism in the coinbase
Script. OP_CCV is the only proposal that satisfies all three requirements from
[Section 9.1](#91-braidpools-requirement): output binding, fraud proof
verification, and SC trust elimination.

**Recursive covenant concerns.** OP_CAT faces opposition primarily due to
concerns about enabling recursive covenants — the worry that unrestricted
Script-level concatenation could enable unforeseen smart contract complexity on
Bitcoin. These concerns are genuine and actively debated; they are not merely
political posturing. The technical argument is that OP_CAT combined with
Schnorr signature verification creates a Turing-complete covenant system, which
some developers view as fundamentally changing Bitcoin's execution model. This
is the primary obstacle to OP_CAT activation, not lack of utility.

**Political landscape.** As of early 2026, no covenant opcode has activated on
mainnet. CTV + CSFS has 66 public signatories expressing support, making it
the closest to potential activation. While this combination alone does not
provide trustless dynamic settlement (see the delegated covenant analysis
above), it does enable the hybrid taproot design where CTV + CSFS provides a
fast path with cryptographic output binding alongside the BitVM2 dispute path.
OP_CCV and OP_TXHASH have smaller constituencies and longer timelines.

**LNHANCE as activation vehicle.** The
[LNHANCE](https://www.lnhance.org/) proposal bundles CTV
([BIP 119](https://github.com/bitcoin/bips/blob/master/bip-0119.mediawiki))
with CSFS
([BIP 348](https://github.com/bitcoin/bips/blob/master/bip-0348.mediawiki)),
OP_INTERNALKEY, and OP_PAIRCOMMIT
([BIP 442](https://github.com/bitcoin/bips/pull/1699)) into a single soft fork.
This bundling is politically strategic: it includes Lightning Network
improvements (LN-Symmetry, simplified PTLCs) alongside covenant capabilities,
broadening the constituency beyond covenant-only use cases. A realistic
community push could emerge by late 2026 or early 2027. For Braidpool, LNHANCE
is the most likely near-term path to getting CTV + CSFS activated.

**Circle STARK verification on Bitcoin.** The
[Bitcoin Wildlife Sanctuary](https://github.com/Bitcoin-Wildlife-Sanctuary/bitcoin-circle-stark)
project (a StarkWare collaboration) has implemented a Circle STARK verifier in
Bitcoin Script, tested on the Catnet signet. The first STARK proof verification
on Bitcoin was completed on July 12, 2024, verifying a squared Fibonacci
sequence at ~790 kvB. Circle STARKs use the Mersenne-31 prime ($2^{31} - 1$),
whose field elements fit in Bitcoin Script's 4-byte (CScriptNum) integers,
though field arithmetic (especially multiplication producing up to 62-bit
intermediates) requires multi-precision emulation via OP_CAT. The verifier
requires OP_CAT (the soft fork dependency) together with the existing OP_SHA256.

The production prover for Circle STARKs is
[Stwo](https://starkware.co/blog/stwo-prover-the-next-gen-of-stark-scaling-is-here/)
(StarkWare), deployed on Starknet mainnet in November 2025. Stwo achieves
940× throughput improvement over its predecessor (Stone), generating proofs in
seconds for computations that previously took minutes. The Circle STARK
protocol avoids heavy algebraic machinery: when $p + 1$ is divisible by a
large power of 2 (as with M31), the circle curve over the prime field provides
the algebraic structure needed for both FFT and FRI, enabling transparent
(no trusted setup) polynomial commitments from hash functions alone.

A newer research direction,
[Binius](https://www.binius.xyz/), operates over binary tower fields (GF(2^k))
rather than prime fields. Binary field addition is a single XOR gate (no carry
propagation), yielding ~5× efficiency over M31 for hash-heavy computations.
Binius is hash-based, transparent, and quantum-resistant like Circle STARKs,
but no Bitcoin Script verifier has been proposed — M31 arithmetic maps to
CScriptNum natively, while binary tower arithmetic would require different
emulation strategies.

If OP_CAT activates, Circle STARK verification in Script replaces the Groth16
SNARK wrapper used by BitVM2. Benefits: no trusted setup ceremony (eliminating
[Open Problem 7](#8-open-problems)), quantum-resistant (hash-based, immune to
Shor's algorithm), and transparent (no structured reference string). Proof
sizes are larger (~50–100 KB vs. ~200 bytes for Groth16), but in BitVM2's
dispute model this proof is only materialized on-chain if someone cheats — the
happy path never posts it. This is the long-term endgame for on-chain fraud
proof verification.

### 9.4 Recommendation

Braidpool should:

1. **Build on BitVM2 now.** The pre-signed transaction graph works today
   (validated by Babylon, Citrea, and Bitlayer in
   [Section 4.9](#49-deployment-validation)) and requires no soft fork.

2. **Adopt CTV + CSFS when available.** If CTV + CSFS activates, add a
   delegated-CTV taproot leaf as a fast settlement path (see the hybrid taproot
   design above). This provides cryptographic output binding for the common case
   where the SC is online and agrees with the operator's UHPO computation, while
   retaining the BitVM2 dispute path for the adversarial case.

3. **Support OP_CAT activation.** OP_CAT is the minimum viable covenant for
   fully trustless output binding — it removes the SC liveness requirement that
   delegated CTV + CSFS retains. OP_TXHASH would also suffice and offers
   cleaner semantics, but OP_CAT has greater deployment maturity. Supporting
   both is reasonable.

4. **Advocate for OP_CCV / MATT.** OP_CCV is uniquely important because it is
   the only covenant proposal that eliminates the SC trust assumption (see
   [Section 9.3](#93-critical-analysis)). Without OP_CCV, a miner with
   $\geq 67\%$ of pool hashrate can control the SC and steal funds via key-path
   spend — this is a critical vulnerability inherited from FROST that no other
   covenant addresses. If OP_CCV activates, the BitVM2 dispute mechanism is
   replaced with a drastically more efficient on-chain fraud proof (~7,000
   vbytes vs. megabytes), coinbases use NUMS internal keys (no exploitable key
   path), and the dispute mechanism is enforced by the Script interpreter rather
   than the SC's honest majority.

5. **Design for graceful upgrade.** Under Direct Coinbase Settlement, each
   coinbase is a standard P2TR output — this format never changes regardless of
   which covenant opcodes become available. Only the connector UTXO and
   settlement template change with new opcodes. The hybrid taproot design
   naturally supports this: each spending path is an independent leaf that can
   be added or replaced as new opcodes become available, while coinbase custody
   remains untouched.

The practical path follows two parallel tracks:

- **Verification track** (how fraud proofs are checked, and trusted setup
  reduced): BitVM2 + Groth16 today (trusted setup, not quantum-safe) →
  Glock DV-SNARK (~2026 target, ~1000× Assert reduction; per-challenger
  setup, not quantum-safe) → Circle STARK with Stwo prover (requires OP_CAT;
  **no trusted setup**, quantum-resistant, ~50–100 KB proofs).
- **Covenant track** (how outputs are bound and SC trust reduced):
  FROST/economic only (SC trust assumption) → LNHANCE CTV + CSFS delegated
  fast path (SC trust preserved) → OP_CAT trustless output binding (SC trust
  for fraud proofs only) → OP_CCV on-chain state machine (**SC trust
  eliminated**; NUMS key path, covenant-enforced settlement).

These tracks are independent — progress on one does not require progress on
the other. Each step within a track reduces trust assumptions and on-chain
costs.

### 9.5 The Output-Binding Impossibility

The analysis above reveals a fundamental impossibility: **without an opcode
that inspects the spending transaction's outputs, no mechanism can enforce
correct UHPO payouts without a trusted online signer.** Every existing approach
either (a) delegates output choice to a signer who must be trusted to choose
correctly (FROST, delegated CTV + CSFS), or (b) verifies computation
correctness but cannot bind that computation's result to the actual transaction
outputs (BitVM2 without covenants). The output-binding gap is not an
implementation limitation — it is a structural property of Bitcoin Script's
current execution model, which receives no information about the spending
transaction beyond the signature and witness.

This motivates the question: what is the *minimal* opcode that closes the gap
for Braidpool's use case? Consider a hypothetical OP_CHECKOUTPUTHASHVERIFY
(OP_COHV) with the following semantics:

```
OP_CHECKOUTPUTHASHVERIFY:
  Pop top stack element (32 bytes, interpreted as SHA256 hash)
  Compute SHA256(serialized_outputs) of the spending transaction
  If they match: continue execution
  If they don't: fail the script
```

This is strictly less powerful than OP_CAT, OP_TXHASH, or OP_CCV. It
introduces transaction introspection — Script can "see" the outputs — without
enabling recursive covenants, sighash reconstruction, or state-carrying UTXOs.

**However, output introspection alone is insufficient.** Consider the
settlement script `<operator_pubkey> OP_CHECKSIGVERIFY OP_COHV` with witness
`<signature> <output_hash>`. The operator chooses both the outputs and the hash
on the witness stack. Since OP_COHV compares `SHA256(outputs)` against the
stack-provided hash, the operator can always satisfy this check trivially by
setting `output_hash = SHA256(whatever_outputs_they_chose)`. **The constraint
is vacuous** — it reduces to plain CHECKSIG.

For output introspection to constrain the operator, the hash must come from
somewhere the operator does not control:

1. **Hardcoded in the scriptPubKey.** This is equivalent to CTV — the hash is
   fixed at UTXO creation time. Useless for Braidpool, where the UHPO
   distribution is unknown until the epoch ends.

2. **Signed by a third party (CSFS).** Script
   `<SC_pubkey> OP_CHECKSIGFROMSTACKVERIFY OP_COHV` verifies that the SC signed
   the output hash, and COHV verifies the outputs match. This collapses to the
   delegated CTV + CSFS pattern already analyzed in
   [Section 9.3](#93-critical-analysis), with the same SC liveness requirement.

3. **Cross-input data: embedded in a BitVM2 connector.** The Assert transaction
   commits the proven-correct output hash into a connector output's
   scriptPubKey. The UHPO payout transaction spends this connector, and the
   connector's script enforces `<embedded_hash> OP_COHV`. This is the only
   scenario where output introspection adds something CSFS cannot provide:
   the hash is committed on-chain by the fraud proof mechanism, not signed by
   a live party. But this requires reading data across inputs — a significantly
   more complex capability than single-input introspection, closer in scope to
   OP_TXHASH or OP_CCV than to a minimal opcode.

**Direct Coinbase Settlement illustrates the impossibility's practical shape.**
Under DCS, the settlement transaction spends ~2016 individual coinbase inputs
(standard P2TR) plus one connector input created by the BitVM2 Assert
transaction. The Assert embeds the proven-correct output hash into the
connector's scriptPubKey. The natural settlement script is:
`<embedded_hash> OP_COHV` on the connector input — verifying that the
transaction's outputs match the fraud-proof-validated UHPO distribution. This
is precisely item 3 above (cross-input data flow): the output hash originates
in the Assert transaction, passes through the connector UTXO, and constrains
the settlement transaction's outputs. DCS does not circumvent the
impossibility; it *demonstrates why cross-input data flow is necessary*. The
coinbase inputs provide funds (standard P2TR, no covenant complexity), while
the connector input provides the validated constraint (requiring
OP_TXHASH/OP_CCV-level capability). This separation of fund custody from
settlement logic is architecturally clean but still requires an opcode that
can read data across inputs — confirming that the minimum viable covenant is
at least as powerful as OP_CAT or OP_TXHASH.

**ColliderScript: an existence proof.** ColliderScript
([Heilman, Kolobov, Levy, Poelstra, 2024](https://eprint.iacr.org/2024/1802))
demonstrates that output binding is theoretically achievable *today* without any
soft fork, via 160-bit hash collisions in SHA-1/RIPEMD-160. The cost — on the
order of $2^{86}$ hash queries per spend, equivalent to approximately 33 hours
of the entire Bitcoin mining network's hash output — makes it wildly
impractical. But it serves as an
existence proof: the impossibility is specific to *efficient* introspection,
not introspection per se. No fundamental cryptographic barrier prevents output
binding; only the absence of a cheap opcode.

**Conclusion.** The impossibility result is robust: closing the output-binding
gap requires either (a) a trusted online signer (FROST, delegated CTV + CSFS),
or (b) a covenant opcode powerful enough to bridge verified computation results
to transaction output enforcement. There is no "minimal" opcode that avoids
both trust and complexity — the simplest sufficient opcodes are OP_CAT (which
enables sighash reconstruction and output verification in a single input's
script) or OP_TXHASH (which provides direct field access). Proposals narrower
than these either collapse to existing mechanisms or require cross-input data
flow that introduces comparable complexity.

## 10. Conclusion

The BitVM2 + risk-taker model with Direct Coinbase Settlement addresses the
biggest weakness of threshold signing for UHPO settlement: liveness. Under the
FROST-only approach, the signing committee must execute a multi-round signing
ceremony for *every block's* coinbase — approximately 2016 ceremonies per
epoch. By replacing this with optimistic verification over individual coinbase
UTXOs, we eliminate per-block signing entirely. The signing committee's role is
reduced to incremental pre-signing of settlement templates as coinbases mature
(height + 100), requiring at most one coordinated action per epoch rather than
one per block.

Each coinbase remains as a standard P2TR UTXO controlled by the SC active when
the block was mined, pre-signed with `SIGHASH_ANYONECANPAY | SIGHASH_NONE` to
decouple spending authorization from settlement structure. At epoch end,
risk-takers settle their own miners in parallel batch transactions, each
spending a subset of coinbase UTXOs. Each batch stays under Bitcoin's 400 KWU
standardness limit, finalizes independently, and shares a single UHPO SNARK
proof with per-batch Merkle inclusion verification. If any coinbase's SC fails
to pre-sign, it is excluded and rolls to the next epoch — providing per-batch
failure isolation.

This comes at two costs. First, the output-binding gap is a new, critical
limitation. We cannot force the operator to execute the correct payouts on-chain
without covenant opcodes. Economic incentives (bond forfeiture, reputation,
future income) mitigate this for rational operators, and the proof-of-payment
mechanism (SPV proof or SC escrow) provides additional verification, but the
gap remains open until a soft fork enabling dynamic output introspection.
Second, the SC honest majority assumption is inherited from FROST and remains
critical: a miner controlling $\geq 67\%$ of pool hashrate can populate the SC
with Sybil identities and steal funds via the taproot key path, bypassing
BitVM2 entirely. OP_CCV ([Section 9.3](#93-critical-analysis)) is the only
covenant proposal that eliminates both limitations — replacing key-path-
spendable coinbases with NUMS-key coinbases whose spending rules are enforced
by an on-chain covenant state machine.

The net assessment: this approach is stronger for pools with active derivatives
markets, where well-capitalized risk-takers serve as natural operators. It is
weaker during bootstrapping, when the FROST fallback is the only option. The
derivatives market described in [derivatives.md](derivatives.md) and the
settlement mechanism are complementary: each strengthens the other. Risk-takers
need a settlement mechanism to claim reimbursement, and the settlement mechanism
needs risk-takers to act as operators.

## References

- [BitVM2: Bridging Bitcoin to Second Layers](https://bitvm.org/bitvm2)
- [BitVM2-Bridge Formal Paper](https://eprint.iacr.org/2025/1158)
- [Glock: Garbled Locks for Bitcoin](https://eprint.iacr.org/2025/1485)
- [Verifier's Dilemma](https://arxiv.org/abs/2312.01549)
- [Hollow Victory Attack](https://arxiv.org/abs/2504.05094)
- [FROST: Flexible Round-Optimized Schnorr Threshold Signatures](https://eprint.iacr.org/2020/852)
- [ROAST: Robust Asynchronous Schnorr Threshold Signatures](https://eprint.iacr.org/2022/550)
- [Braidpool Specification](braidpool_spec.md)
- [Bitcoin Hashrate Derivatives Trading](derivatives.md)
- [General Considerations for Decentralized Mining Pools](general_considerations.md)
- [BIP 119: OP_CTV](https://github.com/bitcoin/bips/blob/master/bip-0119.mediawiki)
- [BIP 346: OP_TXHASH](https://github.com/bitcoin/bips/pull/1500)
- [BIP 347: OP_CAT](https://github.com/bitcoin/bips/blob/master/bip-0347.mediawiki)
- [BIP 348: OP_CSFS](https://github.com/bitcoin/bips/blob/master/bip-0348.mediawiki)
- [BIP 443: OP_CCV](https://github.com/bitcoin/bips/pull/1793)
- [Challenge: Covenants for Braidpool](https://delvingbitcoin.org/t/challenge-covenants-for-braidpool/1370)
- [MATT](https://merkle.fun/)
- [ColliderScript: Covenants in Bitcoin via 160-bit hash collisions](https://eprint.iacr.org/2024/1802)
- [LNHANCE](https://www.lnhance.org/)
- [BIP 442: OP_PAIRCOMMIT](https://github.com/bitcoin/bips/pull/1699)
- [Bitcoin Circle STARK Verifier](https://github.com/Bitcoin-Wildlife-Sanctuary/bitcoin-circle-stark)
- [Starknet x Alpen Labs: Glock Bridge](https://www.starknet.io/blog/starknet-alpen-bitcoin-glock/)
- [Stwo Prover: Next-gen STARK Scaling](https://starkware.co/blog/stwo-prover-the-next-gen-of-stark-scaling-is-here/)
- [Binius: Proofs over Binary Tower Fields](https://www.binius.xyz/)
- [Bulletproofs: Short Proofs for Confidential Transactions](https://eprint.iacr.org/2017/1066)
- [Designated-Verifier zk-SNARKs Made Easy](https://eprint.iacr.org/2024/1153)
- [Applications of Zero-Knowledge Proofs on Bitcoin (Özmiş, 2025)](https://eprint.iacr.org/2025/1271)
- [Plonky3: Polynomial IOP Toolkit](https://github.com/Plonky3/Plonky3)
