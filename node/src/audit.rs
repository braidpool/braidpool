use crate::bead::Bead;
use crate::braid::{AddBeadStatus, Braid};
use bitcoin::consensus::serialize;
use bitcoin::hashes::sha256d;
use bitcoin::BlockHash;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;
use std::time::SystemTime;
use tokio::sync::RwLock;
use tracing::{debug, error, info, warn};

pub const UPSTREAM_EXTRANONCE1_BYTES: usize = 4;
pub const MINER_PREFIX_BYTES: usize = 2;
pub const COMMITMENT_BYTES: usize = 5;
pub const MINER_ROLL_BYTES: usize = 1;
pub const TOTAL_EXTRANONCE1_BYTES: usize =
    UPSTREAM_EXTRANONCE1_BYTES + MINER_PREFIX_BYTES + COMMITMENT_BYTES;

pub type ShareId = BlockHash;

/// Compute composite hash for audit mode: hash(block_header || committed_metadata)
/// This is ONLY used in audit mode where we cannot use OP_RETURN commitments, which
/// we will use as an extranonce commitment.
pub fn compute_audit_bead_hash(bead: &Bead) -> BlockHash {
    let header_bytes = serialize(&bead.block_header);
    let metadata_bytes = serialize(&bead.committed_metadata);
    let mut combined = Vec::with_capacity(header_bytes.len() + metadata_bytes.len());
    combined.extend_from_slice(&header_bytes);
    combined.extend_from_slice(&metadata_bytes);
    BlockHash::from_byte_array(sha256d::Hash::hash(&combined).to_byte_array())
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq)]
pub struct AuditCommitment {
    pub commitment_bytes: [u8; COMMITMENT_BYTES],
    pub parent_bead_hash: Option<BlockHash>,
}

impl Default for AuditCommitment {
    fn default() -> Self {
        Self {
            commitment_bytes: [0u8; COMMITMENT_BYTES],
            parent_bead_hash: None,
        }
    }
}

impl AuditCommitment {
    pub fn genesis() -> Self {
        Self::default()
    }

    pub fn from_audit_bead(bead: &Bead) -> Self {
        let composite_hash = compute_audit_bead_hash(bead);
        Self::from_bead_hash(composite_hash)
    }

    pub fn from_hash_prefix(hash_prefix: &[u8]) -> Self {
        let mut commitment_bytes = [0u8; COMMITMENT_BYTES];
        let len = hash_prefix.len().min(COMMITMENT_BYTES);
        commitment_bytes[..len].copy_from_slice(&hash_prefix[..len]);

        Self {
            commitment_bytes,
            parent_bead_hash: None,
        }
    }

    pub fn from_bead_hash(bead_hash: BlockHash) -> Self {
        let hash_bytes = bead_hash.to_byte_array();
        let mut commitment_bytes = [0u8; COMMITMENT_BYTES];
        commitment_bytes.copy_from_slice(&hash_bytes[..COMMITMENT_BYTES]);

        Self {
            commitment_bytes,
            parent_bead_hash: Some(bead_hash),
        }
    }

    pub fn to_hex(&self) -> String {
        hex::encode(&self.commitment_bytes)
    }

    pub fn verify_in_extranonce1(&self, extranonce1_bytes: &[u8], miner_prefix: &[u8]) -> bool {
        if extranonce1_bytes.len() != TOTAL_EXTRANONCE1_BYTES {
            return false;
        }
        if &extranonce1_bytes
            [UPSTREAM_EXTRANONCE1_BYTES..UPSTREAM_EXTRANONCE1_BYTES + MINER_PREFIX_BYTES]
            != miner_prefix
        {
            return false;
        }
        let commitment_start = UPSTREAM_EXTRANONCE1_BYTES + MINER_PREFIX_BYTES;
        let commitment_end = commitment_start + COMMITMENT_BYTES;
        &extranonce1_bytes[commitment_start..commitment_end] == &self.commitment_bytes
    }

    pub fn extract_miner_prefix_from_ext1(extranonce1_bytes: &[u8]) -> Option<Vec<u8>> {
        if extranonce1_bytes.len() < UPSTREAM_EXTRANONCE1_BYTES + MINER_PREFIX_BYTES {
            return None;
        }
        Some(
            extranonce1_bytes
                [UPSTREAM_EXTRANONCE1_BYTES..UPSTREAM_EXTRANONCE1_BYTES + MINER_PREFIX_BYTES]
                .to_vec(),
        )
    }
}

/// Per miner audit state tracking commitment chain
#[derive(Debug, Clone)]
pub struct MinerAuditState {
    pub current_commitment: AuditCommitment,
    pub miner_prefix: Vec<u8>,
    pub commitment_pending: bool,
    pub previous_commitment: Option<AuditCommitment>,
}

impl MinerAuditState {
    pub fn new(miner_prefix: Vec<u8>) -> Self {
        Self {
            current_commitment: AuditCommitment::genesis(),
            miner_prefix,
            commitment_pending: false,
            previous_commitment: None,
        }
    }

    pub fn update_commitment_audit(&mut self, bead: &Bead) {
        self.previous_commitment = Some(self.current_commitment.clone());
        let composite_hash = compute_audit_bead_hash(bead);
        let new_commitment = AuditCommitment::from_bead_hash(composite_hash);
        info!(
            miner_prefix = %hex::encode(&self.miner_prefix),
            old_commitment = %self.current_commitment.to_hex(),
            new_commitment = %new_commitment.to_hex(),
            block_hash = %bead.block_header.block_hash(),
            composite_hash = %composite_hash,
            "Updating miner audit commitment"
        );
        self.current_commitment = new_commitment;
        self.commitment_pending = true;
    }

    pub fn verify_share(
        &self,
        extranonce1_bytes: &[u8],
        extranonce2_hex: &str,
    ) -> AuditVerificationResult {
        if extranonce1_bytes.len() != TOTAL_EXTRANONCE1_BYTES {
            return AuditVerificationResult::Invalid {
                reason: format!(
                    "Wrong extranonce1 length: expected {} bytes, got {}",
                    TOTAL_EXTRANONCE1_BYTES,
                    extranonce1_bytes.len()
                ),
            };
        }
        if extranonce2_hex.len() != MINER_ROLL_BYTES * 2 {
            return AuditVerificationResult::Invalid {
                reason: format!(
                    "Wrong extranonce2 length: expected {} hex chars, got {}",
                    MINER_ROLL_BYTES * 2,
                    extranonce2_hex.len()
                ),
            };
        }
        if let Some(prefix) = AuditCommitment::extract_miner_prefix_from_ext1(extranonce1_bytes) {
            if prefix != self.miner_prefix {
                return AuditVerificationResult::Invalid {
                    reason: format!(
                        "Miner prefix mismatch: expected {}, got {}",
                        hex::encode(&self.miner_prefix),
                        hex::encode(&prefix)
                    ),
                };
            }
        } else {
            return AuditVerificationResult::Invalid {
                reason: "Could not extract miner prefix from extranonce1".to_string(),
            };
        }
        if self
            .current_commitment
            .verify_in_extranonce1(extranonce1_bytes, &self.miner_prefix)
        {
            let miner_roll = hex::decode(extranonce2_hex)
                .ok()
                .and_then(|bytes| bytes.first().copied());

            AuditVerificationResult::Valid {
                commitment: self.current_commitment.clone(),
                miner_roll,
            }
        } else {
            let commitment_start = UPSTREAM_EXTRANONCE1_BYTES + MINER_PREFIX_BYTES;
            let commitment_end = commitment_start + COMMITMENT_BYTES;
            let actual = hex::encode(&extranonce1_bytes[commitment_start..commitment_end]);

            AuditVerificationResult::Invalid {
                reason: format!(
                    "Commitment mismatch in extranonce1: expected {}, got {}",
                    self.current_commitment.to_hex(),
                    actual
                ),
            }
        }
    }

    pub fn verify_share_with_fallback(
        &self,
        extranonce1_bytes: &[u8],
        extranonce2_hex: &str,
        previous_commitment: Option<&AuditCommitment>,
    ) -> AuditVerificationResult {
        let result = self.verify_share(extranonce1_bytes, extranonce2_hex);
        if matches!(result, AuditVerificationResult::Invalid { .. }) {
            if let Some(prev_commitment) = previous_commitment {
                if prev_commitment.verify_in_extranonce1(extranonce1_bytes, &self.miner_prefix) {
                    warn!(
                        old = %prev_commitment.to_hex(),
                        current = %self.current_commitment.to_hex(),
                        "Share used previous commitment, accepting it as valid under conditions"
                    );
                    return AuditVerificationResult::Valid {
                        commitment: prev_commitment.clone(),
                        miner_roll: hex::decode(extranonce2_hex)
                            .ok()
                            .and_then(|bytes| bytes.first().copied()),
                    };
                }
            }
        }
        result
    }

    pub fn mark_commitment_sent(&mut self) {
        self.commitment_pending = false;
    }
}

#[derive(Debug, Clone)]
pub enum AuditVerificationResult {
    Valid {
        commitment: AuditCommitment,
        miner_roll: Option<u8>,
    },
    Invalid {
        reason: String,
    },
}

/// Links a share to audit verification
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditRecord {
    pub share_id: ShareId,
    pub timestamp: SystemTime,
    pub miner_ip: String,
    pub worker_name: String,
    pub job_id: String,
    pub extranonce2: String,
    pub nonce: String,
    pub ntime: String,
    pub audit_verified: bool,
    pub audit_commitment: Option<AuditCommitment>,
    pub upstream_accepted: Option<bool>,
    pub upstream_eligible: bool,
    pub bead_hash: BlockHash,
}

/// Wraps Braid and adds audit verification layer
pub struct AuditDAG {
    /// The underlying braid structure
    pub braid: Arc<RwLock<Braid>>,
    /// Audit records for shares
    records: HashMap<ShareId, AuditRecord>,
    /// Per miner audit state for commitment verification
    pub miner_states: HashMap<String, MinerAuditState>,
    /// Mapping from composite bead hash to share ID that created it
    bead_to_share: HashMap<BlockHash, ShareId>,
}

impl AuditDAG {
    pub fn new(braid: Arc<RwLock<Braid>>) -> Self {
        Self {
            braid,
            records: HashMap::new(),
            miner_states: HashMap::new(),
            bead_to_share: HashMap::new(),
        }
    }

    pub async fn add_and_record_bead(
        &mut self,
        mut record: AuditRecord,
        bead: Bead,
        extranonce1_bytes: &[u8],
    ) -> Result<(ShareId, bool), String> {
        let share_id = record.share_id.clone();
        let miner_ip = record.miner_ip.clone();
        let composite_hash = compute_audit_bead_hash(&bead);
        if let Some(miner_state) = self.miner_states.get_mut(&miner_ip) {
            let verification = miner_state.verify_share_with_fallback(
                extranonce1_bytes,
                &record.extranonce2,
                miner_state.previous_commitment.as_ref(),
            );
            match verification {
                AuditVerificationResult::Valid {
                    commitment,
                    miner_roll,
                } => {
                    record.audit_commitment = Some(commitment);
                    record.audit_verified = true;
                    debug!(
                        share_id = %share_id,
                        miner = %miner_ip,
                        miner_roll = ?miner_roll,
                        extranonce1 = %hex::encode(extranonce1_bytes),
                        extranonce2 = %record.extranonce2,
                        block_hash = %bead.block_header.block_hash(),
                        composite_hash = %composite_hash,
                        "Bead passed audit verification"
                    );
                }
                AuditVerificationResult::Invalid { reason } => {
                    record.audit_verified = false;
                    error!(
                        share_id = %share_id,
                        miner = %miner_ip,
                        reason = %reason,
                        extranonce1 = %hex::encode(extranonce1_bytes),
                        extranonce2 = %record.extranonce2,
                        "Bead failed audit verification thus rejecting."
                    );
                    return Err(format!("Audit verification failed: {}", reason));
                }
            }
        } else {
            warn!(miner = %miner_ip, "No miner state for audit verification");
            record.audit_verified = false;
            return Err("No miner state".to_string());
        }
        record.bead_hash = composite_hash;
        let mut bead_added = false;
        {
            let mut braid = self.braid.write().await;
            let status = braid.extend(&bead);
            match status {
                AddBeadStatus::BeadAdded => {
                    bead_added = true;
                    info!(
                        block_hash = %bead.block_header.block_hash(),
                        composite_hash = %composite_hash,
                        parents = ?bead.committed_metadata.parents,
                        miner = %miner_ip,
                        "Bead added to braid"
                    );
                }
                AddBeadStatus::DagAlreadyContainsBead => {
                    warn!(
                        composite_hash = %composite_hash,
                        "Bead already in DAG, treating as idempotent success"
                    );
                    // Do not return error as this process can be re-trigger by the same miner who got disconnect
                    // for a reason but and now retrying to submit that share again
                    bead_added = false;
                }
                AddBeadStatus::InvalidBead => {
                    error!(
                        composite_hash = %composite_hash,
                        "Invalid bead"
                    );
                    return Err("Invalid bead".to_string());
                }
                AddBeadStatus::ParentsNotYetReceived => {
                    warn!(
                        composite_hash = %composite_hash,
                        parents = ?bead.committed_metadata.parents,
                        "Parents not yet received, treating as orphan"
                    );
                }
            }
        }
        self.records.insert(share_id.clone(), record);
        self.bead_to_share.insert(composite_hash, share_id.clone());
        info!(
            composite_hash = %composite_hash,
            block_hash = %bead.block_header.block_hash(),
            share_id = %share_id,
            miner = %miner_ip,
            total_beads = %self.records.len(),
            "Bead recorded successfully"
        );
        Ok((share_id, bead_added))
    }

    pub fn mark_upstream_forwarded(&mut self, share_id: &ShareId) {
        if let Some(record) = self.records.get_mut(share_id) {
            record.upstream_eligible = true;
            info!(
                share_id = %share_id,
                "Bead marked as forwarded to upstream"
            );
        }
    }

    pub fn update_upstream_response(&mut self, share_id: &ShareId, accepted: bool) {
        if let Some(record) = self.records.get_mut(share_id) {
            record.upstream_accepted = Some(accepted);
            info!(
                share_id = %share_id,
                accepted = %accepted,
                "Updated upstream response"
            );
        }
    }

    pub fn register_miner(&mut self, miner_ip: String, prefix: Vec<u8>) {
        let prefix_hex = hex::encode(&prefix);
        let state = MinerAuditState::new(prefix);
        self.miner_states.insert(miner_ip.clone(), state);
        info!(
            miner = %miner_ip,
            prefix = %prefix_hex,
            "Registered miner for audit tracking"
        );
    }

    pub fn get_record(&self, share_id: &ShareId) -> Option<&AuditRecord> {
        self.records.get(share_id)
    }

    pub fn get_share_for_bead(&self, bead_hash: &BlockHash) -> Option<&ShareId> {
        self.bead_to_share.get(bead_hash)
    }

    pub fn get_miner_stats(&self, miner_ip: &str) -> MinerStats {
        let miner_records: Vec<&AuditRecord> = self
            .records
            .values()
            .filter(|r| r.miner_ip == miner_ip)
            .collect();

        let total_beads = miner_records.len();
        let upstream_eligible = miner_records.iter().filter(|r| r.upstream_eligible).count();
        let upstream_accepted = miner_records
            .iter()
            .filter(|r| r.upstream_accepted == Some(true))
            .count();
        let upstream_rejected = miner_records
            .iter()
            .filter(|r| r.upstream_accepted == Some(false))
            .count();
        let audit_verified = miner_records.iter().filter(|r| r.audit_verified).count();

        let miner_state = self.miner_states.get(miner_ip);

        MinerStats {
            total_beads,
            audit_verified_beads: audit_verified,
            audit_failed_beads: total_beads - audit_verified,
            upstream_eligible_beads: upstream_eligible,
            upstream_accepted_beads: upstream_accepted,
            upstream_rejected_beads: upstream_rejected,
            current_commitment: miner_state.map(|s| s.current_commitment.to_hex()),
            audit_rate: if total_beads > 0 {
                audit_verified as f64 / total_beads as f64
            } else {
                0.0
            },
            upstream_acceptance_rate: if upstream_eligible > 0 {
                upstream_accepted as f64 / upstream_eligible as f64
            } else {
                0.0
            },
        }
    }
}

#[derive(Debug, Clone)]
pub struct MinerStats {
    pub total_beads: usize,
    pub audit_verified_beads: usize,
    pub audit_failed_beads: usize,
    pub upstream_eligible_beads: usize,
    pub upstream_accepted_beads: usize,
    pub upstream_rejected_beads: usize,
    pub current_commitment: Option<String>,
    pub audit_rate: f64,
    pub upstream_acceptance_rate: f64,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bead::Bead;
    use crate::committed_metadata::CommittedMetadata;
    use crate::uncommitted_metadata::UnCommittedMetadata;
    use bitcoin::{absolute::Time, ecdsa::Signature, EcdsaSighashType};
    use std::str::FromStr;

    fn create_test_bead(parents: Vec<BlockHash>) -> Bead {
        let block: bitcoin::BlockHeader = bitcoin::consensus::deserialize(&hex::decode(
            "0100000000000000000000000000000000000000000000000000000000000000000000003ba3edfd7a7b12b27ac72c3e67768f617fc81bc3888a51323a9fb8aa4b1e5e4a29ab5f49ffff001d1dac2b7c"
        ).unwrap()).unwrap();

        // Create a valid signature for uncommitted metadata
        let hex = "3046022100839c1fbc5304de944f697c9f4b1d01d1faeba32d751c0f7acb21ac8a0f436a72022100e89bd46bb3a5a62adc679f659b7ce876d83ee297c7a5587b2011c4fcc72eab45";
        let sig = Signature {
            signature: secp256k1::ecdsa::Signature::from_str(hex).unwrap(),
            sighash_type: EcdsaSighashType::All,
        };

        Bead {
            block_header: block,
            committed_metadata: CommittedMetadata {
                transaction_ids: crate::committed_metadata::TxIdVec(vec![]),
                parents: parents.into_iter().collect(),
                parent_bead_timestamps: crate::committed_metadata::TimeVec(vec![]),
                payout_address: "bc1qtest".to_string(),
                start_timestamp: Time::from_consensus(1653195600).unwrap(),
                comm_pub_key: bitcoin::PublicKey::from_str(
                    "020202020202020202020202020202020202020202020202020202020202020202",
                )
                .unwrap(),
                min_target: bitcoin::CompactTarget::from_consensus(486604799),
                weak_target: bitcoin::CompactTarget::from_consensus(486604799),
                miner_ip: "127.0.0.1".to_string(),
            },
            uncommitted_metadata: UnCommittedMetadata {
                extra_nonce_1: 42,
                extra_nonce_2: 42,
                broadcast_timestamp: Time::from_consensus(1653195600).unwrap(),
                signature: sig,
            },
        }
    }

    /// Helper to construct a strictly valid 11-byte extranonce1 array
    fn build_extranonce1(upstream: &[u8], prefix: &[u8], commitment: &[u8]) -> Vec<u8> {
        let mut ext1 = Vec::with_capacity(TOTAL_EXTRANONCE1_BYTES);
        ext1.extend_from_slice(upstream);
        ext1.extend_from_slice(prefix);
        ext1.extend_from_slice(commitment);
        ext1
    }

    #[test]
    /// Verify the conversion of composite hash into commitment
    fn test_audit_commitment_from_bead_hash() {
        let hash =
            BlockHash::from_str("000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f")
                .unwrap();

        let commitment = AuditCommitment::from_bead_hash(hash);
        assert_eq!(commitment.commitment_bytes.len(), COMMITMENT_BYTES);
        assert_eq!(commitment.parent_bead_hash, Some(hash));
        assert_eq!(
            &commitment.commitment_bytes,
            &hash.to_byte_array()[..COMMITMENT_BYTES]
        );
    }

    #[test]
    /// Verify that hash the exact same bead twice, leads to the exact same result.
    fn test_compute_audit_bead_hash_deterministic() {
        let bead = create_test_bead(vec![]);
        let hash1 = compute_audit_bead_hash(&bead);
        let hash2 = compute_audit_bead_hash(&bead);
        assert_eq!(hash1, hash2, "Hash should be deterministic");
    }

    #[test]
    /// Verify that changing the parents of a bead leads to an entirely new hash.
    fn test_compute_audit_bead_hash_different_parents() {
        let parent1 =
            BlockHash::from_str("000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f")
                .unwrap();
        let parent2 =
            BlockHash::from_str("00000000839a8e6886ab5951d76f411475428afc90947ee320161bbf18eb6048")
                .unwrap();

        let bead1 = create_test_bead(vec![parent1]);
        let bead2 = create_test_bead(vec![parent2]);

        let hash1 = compute_audit_bead_hash(&bead1);
        let hash2 = compute_audit_bead_hash(&bead2);

        assert_ne!(
            hash1, hash2,
            "Different parents should produce different hashes"
        );
    }

    #[test]
    /// Verify that the node accepts the perfectly constructed 11 byte extranonce.
    fn test_verify_in_extranonce1_valid() {
        let miner_prefix = vec![0xaa, 0xbb];
        let commitment = AuditCommitment::from_hash_prefix(&[0x11, 0x22, 0x33, 0x44, 0x55]);
        let extranonce1 = build_extranonce1(
            &[0xff; UPSTREAM_EXTRANONCE1_BYTES],
            &miner_prefix,
            &commitment.commitment_bytes,
        );

        assert!(commitment.verify_in_extranonce1(&extranonce1, &miner_prefix));
    }

    #[test]
    /// Verify that if an ASIC submits an extranonce with unspecified bytes lenght, the node rejects it.
    fn test_verify_in_extranonce1_wrong_length() {
        let commitment = AuditCommitment::genesis();
        let extranonce1 = vec![0xff; 5]; // Too short
        let miner_prefix = vec![0xaa, 0xbb];

        assert!(!commitment.verify_in_extranonce1(&extranonce1, &miner_prefix));
    }

    #[test]
    /// Verify that if Miner A tries to submit work using Miner B's 2 byte prefix, the node catches the theft and rejects it.
    fn test_verify_in_extranonce1_wrong_prefix() {
        let miner_prefix = vec![0xaa, 0xbb];
        let wrong_prefix = vec![0xcc, 0xdd];
        let commitment = AuditCommitment::from_hash_prefix(&[0x11, 0x22, 0x33, 0x44, 0x55]);
        let extranonce1 = build_extranonce1(
            &[0xff; UPSTREAM_EXTRANONCE1_BYTES],
            &wrong_prefix,
            &commitment.commitment_bytes,
        );

        assert!(!commitment.verify_in_extranonce1(&extranonce1, &miner_prefix));
    }

    #[test]
    /// Verify that if the miner submits work for an old or non existed DAG tip, the node rejects it.
    fn test_verify_in_extranonce1_wrong_commitment() {
        let miner_prefix = vec![0xaa, 0xbb];
        let commitment = AuditCommitment::from_hash_prefix(&[0x11, 0x22, 0x33, 0x44, 0x55]);
        let wrong_commitment = [0x66, 0x77, 0x88, 0x99, 0xaa];

        let extranonce1 = build_extranonce1(
            &[0xff; UPSTREAM_EXTRANONCE1_BYTES],
            &miner_prefix,
            &wrong_commitment,
        );

        assert!(!commitment.verify_in_extranonce1(&extranonce1, &miner_prefix));
    }

    #[test]
    /// Verify that the 2 byte miner prefix is extractable from the 11 bytes of the extranonce1 array.
    fn test_extract_miner_prefix_valid() {
        let miner_prefix = vec![0xaa, 0xbb];
        let extranonce1 = build_extranonce1(
            &[0xff; UPSTREAM_EXTRANONCE1_BYTES],
            &miner_prefix,
            &[0x11, 0x22, 0x33, 0x44, 0x55],
        );

        let extracted = AuditCommitment::extract_miner_prefix_from_ext1(&extranonce1);
        assert_eq!(extracted, Some(miner_prefix));
    }

    #[test]
    /// Verify that on a new job arrival, the old commitment and the new one update correctly.
    fn test_miner_audit_state_update_commitment() {
        let prefix = vec![0xaa, 0xbb];
        let mut state = MinerAuditState::new(prefix);
        let bead = create_test_bead(vec![]);

        let old_commitment = state.current_commitment.clone();
        state.update_commitment_audit(&bead);

        assert_ne!(state.current_commitment.to_hex(), old_commitment.to_hex());
        assert!(state.commitment_pending);
        assert_eq!(
            state.previous_commitment.unwrap().to_hex(),
            old_commitment.to_hex()
        );
    }

    #[test]
    /// Validate that the incoming share contains the unaltered and valid prefix.
    fn test_verify_share_prefix_mismatch() {
        let prefix = vec![0xaa, 0xbb];
        let state = MinerAuditState::new(prefix);

        let extranonce1 = build_extranonce1(
            &[0xff; UPSTREAM_EXTRANONCE1_BYTES],
            &[0xcc, 0xdd],
            &[0x11, 0x22, 0x33, 0x44, 0x55],
        );
        let result = state.verify_share(&extranonce1, "00");

        match result {
            AuditVerificationResult::Invalid { reason } => {
                assert!(reason.contains("Miner prefix mismatch"))
            }
            _ => panic!("Expected Invalid result"),
        }
    }

    #[test]
    /// Verify that the correct share was successfully accepted and marked as valid.
    fn test_verify_share_valid() {
        let prefix = vec![0xaa, 0xbb];
        let state = MinerAuditState::new(prefix.clone());

        let extranonce1 = build_extranonce1(
            &[0xff; UPSTREAM_EXTRANONCE1_BYTES],
            &prefix,
            &state.current_commitment.commitment_bytes,
        );
        let result = state.verify_share(&extranonce1, "42");

        match result {
            AuditVerificationResult::Valid {
                commitment,
                miner_roll,
            } => {
                assert_eq!(commitment.to_hex(), state.current_commitment.to_hex());
                assert_eq!(miner_roll, Some(0x42));
            }
            _ => panic!("Expected Valid result"),
        }
    }

    #[test]
    /// Validate the hardware buffer latency edge cases where a job uses the previous commitment.
    fn test_verify_share_with_fallback_uses_previous() {
        let prefix = vec![0xaa, 0xbb];
        let mut state = MinerAuditState::new(prefix.clone());

        let extranonce1 = build_extranonce1(
            &[0xff; UPSTREAM_EXTRANONCE1_BYTES],
            &prefix,
            &state.current_commitment.commitment_bytes,
        );
        let bead = create_test_bead(vec![]);
        state.update_commitment_audit(&bead);

        let result = state.verify_share_with_fallback(
            &extranonce1,
            "00",
            state.previous_commitment.as_ref(),
        );

        assert!(
            matches!(result, AuditVerificationResult::Valid { .. }),
            "Expected Valid result with fallback"
        );
    }

    #[test]
    /// Verify a new connected miner is assigned with a new dedicated memory space
    fn test_audit_dag_register_miner() {
        let braid = Arc::new(RwLock::new(Braid::new(vec![])));
        let mut audit_dag = AuditDAG::new(braid);

        let miner_ip = "192.168.1.100".to_string();
        let prefix = vec![0xaa, 0xbb];

        audit_dag.register_miner(miner_ip.clone(), prefix.clone());
        assert_eq!(audit_dag.miner_states[&miner_ip].miner_prefix, prefix);
    }

    #[test]
    /// Verify the share acceptance, rejection and stats calculation logic.
    fn test_miner_stats_calculations() {
        let braid = Arc::new(RwLock::new(Braid::new(vec![])));
        let mut audit_dag = AuditDAG::new(braid);
        let miner_ip = "192.168.1.100".to_string();

        audit_dag.register_miner(miner_ip.clone(), vec![0x00, 0x01]);

        // Insert exactly 10 test records with various states
        for i in 0..10 {
            let hash = BlockHash::from_byte_array([i as u8; 32]);
            let record = AuditRecord {
                share_id: hash,
                timestamp: SystemTime::now(),
                miner_ip: miner_ip.clone(),
                worker_name: "worker1".to_string(),
                job_id: format!("job{}", i),
                extranonce2: "00".to_string(),
                nonce: "00000000".to_string(),
                ntime: "00000000".to_string(),
                audit_verified: i < 8, // 8 verified, 2 failed
                audit_commitment: None,
                upstream_accepted: if i < 5 { Some(true) } else { None }, // 5 accepted
                upstream_eligible: i < 7,                                 // 7 eligible
                bead_hash: hash,
            };
            audit_dag.records.insert(hash, record);
        }

        let stats = audit_dag.get_miner_stats(&miner_ip);

        assert_eq!(stats.total_beads, 10);
        assert_eq!(stats.audit_verified_beads, 8);
        assert_eq!(stats.audit_failed_beads, 2);
        assert_eq!(stats.upstream_eligible_beads, 7);
        assert_eq!(stats.upstream_accepted_beads, 5);
        assert_eq!(stats.audit_rate, 0.8);
        assert_eq!(stats.upstream_acceptance_rate, 5.0 / 7.0);
    }
}
