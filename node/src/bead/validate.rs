//! Checks applied to beads received from peers or RPC before they enter the braid.
//!
//! Timestamp ordering and transaction conflicts are intentionally not checked
//! here: consensus ordering stays timestamp-independent. Target-range / difficulty
//! adjustment, gossipsub policy, genesis policy, and Schnorr signatures are
//! separate work and plug into [`validate_bead`] later.

use std::collections::HashSet;

use bitcoin::Target;

use crate::bead::Bead;
use crate::config::PoolNetwork;
use crate::error::BeadValidationError;

/// Checks a received bead before it is added to the braid.
///
/// The header hash, under `network`'s rules, must meet `header.bits`. Parents
/// must be unique, and `parent_bead_timestamps` must have one entry per parent.
///
/// # Arguments
/// * `bead` - The bead received from gossip, bead-sync, or `addbead`.
/// * `network` - Network whose block-hash rules apply.
///
/// # Returns
/// `Ok(())` when every check passes.
///
/// # Errors
/// [`BeadValidationError`] when any check fails. The caller must drop the bead
/// without parking it, persisting it, or increasing the sender's peer score.
pub fn validate_bead(bead: &Bead, network: PoolNetwork) -> Result<(), BeadValidationError> {
    let header = &bead.block_header;
    let target = Target::from_compact(header.bits);
    if !target.is_met_by(network.block_hash(header)) {
        return Err(BeadValidationError::InsufficientProofOfWork);
    }

    let parents = &bead.committed_metadata.parents;
    let mut seen_parents = HashSet::with_capacity(parents.len());
    if parents.iter().any(|parent| !seen_parents.insert(parent)) {
        return Err(BeadValidationError::DuplicateParents);
    }

    let timestamps = bead.committed_metadata.parent_bead_timestamps.0.len();
    if timestamps != parents.len() {
        return Err(BeadValidationError::ParentTimestampCountMismatch {
            parents: parents.len(),
            timestamps,
        });
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::utils::create_test_bead;
    use bitcoin::CompactTarget;

    fn assert_variant(result: Result<(), BeadValidationError>, expected: &BeadValidationError) {
        match result {
            Err(error) => assert_eq!(&error, expected),
            Ok(()) => panic!("expected {expected}, validation succeeded"),
        }
    }

    #[test]
    fn validate_bead_accepts_a_bead_with_real_proof_of_work() {
        let bead = create_test_bead(1, None);
        assert!(validate_bead(&bead, PoolNetwork::Cpunet).is_ok());
    }

    #[test]
    fn validate_bead_rejects_missing_proof_of_work() {
        let mut bead = create_test_bead(1, None);
        bead.block_header.bits = CompactTarget::from_consensus(0x03000001);
        assert_variant(
            validate_bead(&bead, PoolNetwork::Cpunet),
            &BeadValidationError::InsufficientProofOfWork,
        );
    }

    #[test]
    fn validate_bead_rejects_duplicate_parents() {
        let parent = create_test_bead(1, None);
        let parent_hash = PoolNetwork::Cpunet.block_hash(&parent.block_header);
        let mut bead = create_test_bead(2, Some(parent_hash));
        let timestamp = bead.committed_metadata.parent_bead_timestamps.0[0];
        bead.committed_metadata.parents.push(parent_hash);
        bead.committed_metadata
            .parent_bead_timestamps
            .0
            .push(timestamp);

        assert_variant(
            validate_bead(&bead, PoolNetwork::Cpunet),
            &BeadValidationError::DuplicateParents,
        );
    }

    #[test]
    fn validate_bead_rejects_parent_timestamp_count_mismatch() {
        let parent = create_test_bead(1, None);
        let parent_hash = PoolNetwork::Cpunet.block_hash(&parent.block_header);
        let mut bead = create_test_bead(2, Some(parent_hash));
        bead.committed_metadata.parent_bead_timestamps.0.clear();

        assert_variant(
            validate_bead(&bead, PoolNetwork::Cpunet),
            &BeadValidationError::ParentTimestampCountMismatch {
                parents: 1,
                timestamps: 0,
            },
        );
    }
}
