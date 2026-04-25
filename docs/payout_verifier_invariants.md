# Payout Verifier Invariants (v1alpha)

This document defines the invariant scaffold for a deterministic payout verification pipeline.
The goal is to verify whether candidate RCA/UHPO payout artifacts are consistent with reconstructed
braid state and accounting rules.

## Scope

- The rules below are implementation targets for the payout verifier.
- The current `v1alpha` ruleset is intentionally narrow and verification-first.
- Full signing protocol behavior (FROST/ROAST orchestration) is out of scope.

## Invariants

| ID | Name | Description | Verification Intent |
| --- | --- | --- | --- |
| INV-001 | Value Conservation | Value flow must conserve amounts across payout transitions. | Reject payouts with mismatched input/output value accounting. |
| INV-002 | RCA Ancestry Correctness | Candidate RCA must spend the previously agreed RCA lineage. | Prevent invalid branch spending and payout history divergence. |
| INV-003 | Coinbase Maturity Window | Eligible coinbase inputs must satisfy maturity policy constraints. | Block premature payout spend construction. |
| INV-004 | Miner Allocation Exactness | Candidate miner outputs must match expected accounting snapshot balances. | Prevent under/overpayment for any miner participant. |
| INV-005 | Deterministic Output Ordering | Payout outputs must follow canonical deterministic ordering. | Ensure stable serialization and hash reproducibility. |
| INV-006 | Epoch Boundary Correctness | Settled contributions must belong to allowed accounting windows only. | Prevent leakage across epochs or incorrect settlement windows. |
| INV-007 | Commitment Integrity | Metadata commitments must match reconstructed payout state commitments. | Detect tampering or inconsistent commitment materialization. |
| INV-008 | Dust/Min Output Policy | Outputs must satisfy minimum policy constraints for standardness/usability. | Reject economically unusable payout fragments. |
| INV-009 | No Phantom Recipients | Candidate recipients must exist in the accounting state for the snapshot. | Prevent unauthorized recipient insertion. |
| INV-010 | Replay Stability | Same snapshot and ruleset must yield identical verification hash/status. | Guarantee deterministic verifier behavior across repeated runs. |

## Error Model

Verifier implementations should emit:

- an invariant identifier (`INV-00X`)
- a machine-readable reason code/message
- optional context for debugging (snapshot ID, epoch, candidate hash)

## Execution Modes

- **strict**: fail closed if required data is missing
- **unresolved**: return unresolved status when completeness assumptions are not met

## Notes for Incremental Implementation

1. Implement INV-001 and INV-010 first to establish accounting and determinism baselines.
2. Keep ruleset versioning explicit (`v1alpha`) in all reports.
3. Treat this document as the source of truth for verifier test planning.
