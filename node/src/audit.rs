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

#[derive(Debug, Clone, Serialize, Deserialize)]
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
