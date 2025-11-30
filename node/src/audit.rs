use bitcoin::hashes::sha256;
use bitcoin::{BlockHash, CompactTarget};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::time::SystemTime;
use tracing::{info, warn};
#[derive(Debug, Clone, Serialize, Deserialize, Hash, Eq, PartialEq)]
pub struct ShareId(pub [u8; 32]);

impl ShareId {
    pub fn from_share(
        job_id: &str,
        extranonce2: &str,
        nonce: &str,
        ntime: &str,
        worker_name: &str,
    ) -> Self {
        let mut engine = sha256::Hash::engine();
        bitcoin::hashes::HashEngine::input(&mut engine, job_id.as_bytes());
        bitcoin::hashes::HashEngine::input(&mut engine, extranonce2.as_bytes());
        bitcoin::hashes::HashEngine::input(&mut engine, nonce.as_bytes());
        bitcoin::hashes::HashEngine::input(&mut engine, ntime.as_bytes());
        bitcoin::hashes::HashEngine::input(&mut engine, worker_name.as_bytes());
        let result = sha256::Hash::from_engine(engine);
        let mut id = [0u8; 32];
        id.copy_from_slice(result.as_ref());
        ShareId(id)
    }
}

impl std::fmt::Display for ShareId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", hex::encode(&self.0[..8]))
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct AuditRecord {
    pub share_id: ShareId,
    pub timestamp: SystemTime,
    pub miner_ip: String,
    pub worker_name: String,
    pub job_id: String,
    pub share_difficulty: CompactTarget,
    pub extranonce2: String,
    pub nonce: String,
    pub ntime: String,
    pub block_hash: Option<BlockHash>,
    pub valid: bool,
    pub upstream_accepted: Option<bool>,
    pub parent_shares: Vec<ShareId>,
}

pub struct AuditDAG {
    records: HashMap<ShareId, AuditRecord>,
    latest_shares: HashMap<String, ShareId>,
}

impl AuditDAG {
    pub fn new() -> Self {
        Self {
            records: HashMap::new(),
            latest_shares: HashMap::new(),
        }
    }

    pub async fn add_record(&mut self, mut record: AuditRecord) -> Result<ShareId, String> {
        let share_id = record.share_id.clone();

        if let Some(parent_id) = self.latest_shares.get(&record.miner_ip) {
            record.parent_shares.push(parent_id.clone());
        }

        info!(
            "Recording share {} from {} (job: {}, parents: {})",
            share_id,
            record.worker_name,
            record.job_id,
            record.parent_shares.len()
        );

        // Update latest share for this miner
        self.latest_shares
            .insert(record.miner_ip.clone(), share_id.clone());

        // Store the record
        self.records.insert(share_id.clone(), record);

        info!("Audit DAG now contains {} records", self.records.len());

        Ok(share_id)
    }

    pub fn update_upstream_result(&mut self, share_id: &ShareId, accepted: bool) {
        if let Some(record) = self.records.get_mut(share_id) {
            record.upstream_accepted = Some(accepted);
            info!(
                "Updated share {} upstream_accepted = {}",
                share_id, accepted
            );
        } else {
            warn!("Cannot update share {} - not found in record", share_id);
        }
    }

    pub fn get_miner_stats(&self, miner_ip: &str) -> MinerStats {
        let miner_records: Vec<&AuditRecord> = self
            .records
            .values()
            .filter(|r| r.miner_ip == miner_ip)
            .collect();

        let total_shares = miner_records.len();
        let valid_shares = miner_records.iter().filter(|r| r.valid).count();
        let accepted_shares = miner_records
            .iter()
            .filter(|r| r.upstream_accepted == Some(true))
            .count();
        let rejected_shares = miner_records
            .iter()
            .filter(|r| r.upstream_accepted == Some(false))
            .count();
        let pending_shares = miner_records
            .iter()
            .filter(|r| r.upstream_accepted.is_none())
            .count();

        MinerStats {
            total_shares,
            valid_shares,
            accepted_shares,
            rejected_shares,
            pending_shares,
            rejection_rate: if total_shares > 0 {
                rejected_shares as f64 / total_shares as f64
            } else {
                0.0
            },
        }
    }

    pub fn len(&self) -> usize {
        self.records.len()
    }
}

#[derive(Debug, Clone)]
pub struct MinerStats {
    pub total_shares: usize,
    pub valid_shares: usize,
    pub accepted_shares: usize,
    pub rejected_shares: usize,
    pub pending_shares: usize,
    pub rejection_rate: f64,
}
