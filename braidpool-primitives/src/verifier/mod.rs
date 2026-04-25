use std::collections::BTreeMap;

/// High-level status emitted by verifier implementations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VerificationStatus {
    Pass,
    Fail,
    Unresolved,
}

/// Invariant identifiers for the payout verification pipeline.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum InvariantId {
    Inv001ValueConservation,
    Inv002RcaAncestryCorrectness,
    Inv003CoinbaseMaturityWindow,
    Inv004MinerAllocationExactness,
    Inv005DeterministicOutputOrdering,
    Inv006EpochBoundaryCorrectness,
    Inv007CommitmentIntegrity,
    Inv008DustMinOutputPolicy,
    Inv009NoPhantomRecipients,
    Inv010ReplayStability,
}

/// Machine-readable verification issue with an invariant mapping.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationIssue {
    pub invariant: InvariantId,
    pub detail: String,
}

/// Summary object used by CLI/API adapters.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VerificationReport {
    pub ruleset: String,
    pub status: VerificationStatus,
    pub determinism_hash: Option<String>,
    pub issues: Vec<VerificationIssue>,
}

/// Minimal, implementation-agnostic input needed for payout verification.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PayoutVerificationInput {
    pub snapshot_id: String,
    pub epoch_id: u64,
    pub expected_payout_hash: String,
    pub candidate_payout_hash: String,
}

/// Optional invariant-level outcomes to help with diagnostics and reports.
pub type InvariantResults = BTreeMap<InvariantId, bool>;

/// Core trait for the deterministic payout verifier.
///
/// The production implementation should:
/// - deterministically reconstruct expected payout state
/// - validate candidate payout artifacts against invariant checks
/// - produce stable results for the same input snapshot/ruleset
pub trait PayoutVerifier {
    fn ruleset(&self) -> &str;

    fn verify(&self, input: &PayoutVerificationInput) -> VerificationReport;

    fn evaluate_invariants(&self, input: &PayoutVerificationInput) -> InvariantResults;
}

#[cfg(test)]
mod tests {
    use super::*;

    struct NoopVerifier;

    impl PayoutVerifier for NoopVerifier {
        fn ruleset(&self) -> &str {
            "v1alpha"
        }

        fn verify(&self, _input: &PayoutVerificationInput) -> VerificationReport {
            VerificationReport {
                ruleset: self.ruleset().to_string(),
                status: VerificationStatus::Unresolved,
                determinism_hash: None,
                issues: Vec::new(),
            }
        }

        fn evaluate_invariants(&self, _input: &PayoutVerificationInput) -> InvariantResults {
            BTreeMap::new()
        }
    }

    #[test]
    fn verifier_scaffold_has_stable_ruleset_name() {
        let verifier = NoopVerifier;
        assert_eq!(verifier.ruleset(), "v1alpha");
    }

    #[test]
    #[ignore = "red scaffold: enable once value-conservation check is implemented"]
    fn inv001_value_conservation_red_test() {
        // This intentionally fails to demonstrate expected red-test behavior for INV-001.
        assert!(false, "expected value conservation enforcement to fail until implemented");
    }

    #[test]
    #[ignore = "red scaffold: enable once replay-stability check is implemented"]
    fn inv010_replay_stability_red_test() {
        // This intentionally fails to demonstrate expected red-test behavior for INV-010.
        assert!(
            false,
            "expected replay stability check to fail until deterministic hash pipeline exists"
        );
    }
}
