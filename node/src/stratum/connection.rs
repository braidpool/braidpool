use std::collections::{HashMap, VecDeque};

use bitcoin::hashes::Hash as _;
use tokio::sync::mpsc;
#[allow(unused_imports)]
use tracing::{debug, error, info, trace, warn};

use super::{COMMITMENT_SIZE, DISCONNECT_SIGNAL, PREFIX_BYTES_SIZE};

const PREFIX_EXHAUSTION_WARNING_THRESHOLD: u16 = 60000;
const PREFIX_MAX_VALUE: u16 = u16::MAX;

#[derive(Debug, Clone)]
pub struct PrefixStats {
    pub total_assigned: usize,
    pub available_for_reuse: usize,
    pub next_new_prefix: u16,
    pub total_capacity: u16,
}

impl PrefixStats {
    pub fn utilization_percentage(&self) -> f64 {
        (self.total_assigned as f64 / self.total_capacity as f64) * 100.0
    }
}

pub enum ControlMsg {
    UpdateExtranonce(Vec<u8>),
}

/// Connection information associated with each downstream peer.
#[derive(Debug, Clone)]
pub struct ConnectionInfo {
    pub connection_id: u32,
    pub sender: mpsc::Sender<String>,
    pub control_tx: mpsc::Sender<ControlMsg>,
}

#[derive(Debug, Clone)]
pub struct ConnectionMapping {
    pub downstream_channel_mapping: HashMap<String, ConnectionInfo>,
    pub upstream_extranonce1: Option<String>,
    pub upstream_extranonce2_size: Option<usize>,
    pub upstream_difficulty: Option<f64>,
    worker_to_peer: HashMap<String, String>,
    pub upstream_connected: bool,
    next_extranonce2_prefix: u16,
    pub assigned_prefixes: HashMap<String, u16>,
    available_prefixes: VecDeque<u16>,
    pub current_bead_commitment: Vec<u8>,
}

impl ConnectionMapping {
    pub fn new() -> Self {
        ConnectionMapping {
            downstream_channel_mapping: HashMap::new(),
            upstream_extranonce1: None,
            upstream_extranonce2_size: None,
            upstream_difficulty: None,
            worker_to_peer: HashMap::new(),
            upstream_connected: false,
            next_extranonce2_prefix: 1,
            assigned_prefixes: HashMap::new(),
            available_prefixes: VecDeque::new(),
            current_bead_commitment: vec![0u8; COMMITMENT_SIZE],
        }
    }

    pub fn update_bead_commitment(&mut self, bead_hash: bitcoin::BlockHash) {
        let hash_bytes = bead_hash.to_byte_array();
        self.current_bead_commitment = hash_bytes[..COMMITMENT_SIZE].to_vec();
        info!(
            commitment = %hex::encode(&self.current_bead_commitment),
            bead_hash = %bead_hash,
            "Updated global bead commitment"
        );
    }

    pub fn get_current_bead_commitment(&self) -> Vec<u8> {
        self.current_bead_commitment.clone()
    }

    /// Allocate a unique 2-byte prefix for a new miner in audit mode.
    pub fn allocate_extranonce2_prefix(&mut self) -> (Vec<u8>, usize) {
        let prefix = if let Some(reused_prefix) = self.available_prefixes.pop_front() {
            debug!(
                prefix = %hex::encode(reused_prefix.to_be_bytes()),
                available_count = %self.available_prefixes.len(),
                "Reusing released prefix"
            );
            reused_prefix
        } else {
            let new_prefix: u16 = self.next_extranonce2_prefix;
            self.next_extranonce2_prefix = self.next_extranonce2_prefix.wrapping_add(1);

            if self.next_extranonce2_prefix == 0 {
                warn!("Extranonce2 prefix wrapped around to 0, resetting to 1");
                self.next_extranonce2_prefix = 1;
            }

            if self.next_extranonce2_prefix > PREFIX_EXHAUSTION_WARNING_THRESHOLD
                && self.available_prefixes.is_empty()
            {
                warn!(
                    used_prefixes = %self.next_extranonce2_prefix,
                    total_capacity = PREFIX_MAX_VALUE,
                    "Approaching prefix exhaustion!"
                );
            }

            new_prefix
        };

        let prefix_bytes = prefix.to_be_bytes().to_vec();
        let miner_size = self
            .upstream_extranonce2_size
            .expect("Upstream extranonce2 size must be set before allocating prefix")
            .saturating_sub(PREFIX_BYTES_SIZE);

        debug!(
            prefix = %hex::encode(&prefix_bytes),
            miner_extranonce2_size = %miner_size,
            allocation_type = if self.available_prefixes.len() > 0 { "reused" } else { "new" },
            available_count = %self.available_prefixes.len(),
            "Allocated extranonce2 prefix"
        );

        (prefix_bytes, miner_size)
    }

    pub fn register_prefix(&mut self, peer_addr: String, prefix: u16) {
        if let Some(old_prefix) = self.assigned_prefixes.insert(peer_addr.clone(), prefix) {
            warn!(
                peer = %peer_addr,
                old_prefix = %hex::encode(old_prefix.to_be_bytes()),
                new_prefix = %hex::encode(prefix.to_be_bytes()),
                "Peer reconnected and received new prefix"
            );
        }
        debug!(
            peer = %peer_addr,
            prefix = %hex::encode(prefix.to_be_bytes()),
            total_assigned = %self.assigned_prefixes.len(),
            "Registered prefix assignment"
        );
    }

    fn release_prefix(&mut self, peer_addr: &str) {
        if let Some(prefix) = self.assigned_prefixes.remove(peer_addr) {
            if prefix < PREFIX_MAX_VALUE {
                self.available_prefixes.push_back(prefix);
                info!(
                    peer = %peer_addr,
                    prefix = %hex::encode(prefix.to_be_bytes()),
                    available_count = %self.available_prefixes.len(),
                    "Released prefix for reuse"
                );
            } else {
                warn!(
                    peer = %peer_addr,
                    prefix = %hex::encode(prefix.to_be_bytes()),
                    "Prefix too high, not reusing (near wrap-around range)"
                );
            }
        }
    }

    pub fn get_prefix_stats(&self) -> PrefixStats {
        PrefixStats {
            total_assigned: self.assigned_prefixes.len(),
            available_for_reuse: self.available_prefixes.len(),
            next_new_prefix: self.next_extranonce2_prefix,
            total_capacity: PREFIX_MAX_VALUE,
        }
    }

    pub fn set_upstream_connected(&mut self, connected: bool) {
        self.upstream_connected = connected;
        if connected {
            info!("Upstream marked as connected");
        } else {
            warn!("Upstream marked as disconnected");
        }
    }

    pub fn remove_peer(&mut self, peer_addr: &str) {
        self.release_prefix(peer_addr);
        self.downstream_channel_mapping.remove(peer_addr);
        self.worker_to_peer
            .retain(|_worker_name, mapped_peer| mapped_peer != peer_addr);
        debug!(
            peer = %peer_addr,
            remaining_peers = %self.downstream_channel_mapping.len(),
            available_prefixes = %self.available_prefixes.len(),
            "Removed peer and associated workers"
        );
    }

    pub async fn disconnect_all_with_message(&mut self, reason: &str) {
        let peers: Vec<(String, ConnectionInfo)> =
            self.downstream_channel_mapping.drain().collect();

        for (peer_addr, connection_info) in peers {
            self.release_prefix(&peer_addr);

            let error_msg = serde_json::json!({
                "id": null,
                "result": null,
                "error": [20, reason, null]
            });
            let _ = connection_info
                .sender
                .try_send(serde_json::to_string(&error_msg).unwrap());
            let _ = connection_info
                .sender
                .try_send(DISCONNECT_SIGNAL.to_string());
            info!(
                peer = %peer_addr,
                connection_id = %connection_info.connection_id,
                reason = %reason,
                "Sent shutdown notice to miner"
            );
        }

        debug!(
            available_prefixes = %self.available_prefixes.len(),
            "All miners disconnected, prefixes released"
        );
        self.worker_to_peer.clear();
    }

    pub fn disconnect_peer(&mut self, peer_addr: &str, reason: &str) {
        self.release_prefix(peer_addr);

        if let Some(connection_info) = self.downstream_channel_mapping.remove(peer_addr) {
            info!(
                peer = %peer_addr,
                connection_id = %connection_info.connection_id,
                reason = %reason,
                "Disconnecting miner..."
            );
            let _ = connection_info
                .sender
                .try_send(DISCONNECT_SIGNAL.to_string());
            drop(connection_info);
            info!(peer = %peer_addr, "Miner disconnected (Signal Sent & Channel Dropped)");
        } else {
            warn!(peer = %peer_addr, "Peer not found in connection mapping");
        }

        self.worker_to_peer
            .retain(|_worker_name, mapped_peer| mapped_peer != peer_addr);
    }

    pub fn set_upstream_extranonce(&mut self, extranonce1: String, extranonce2_size: usize) {
        self.upstream_extranonce1 = Some(extranonce1);
        self.upstream_extranonce2_size = Some(extranonce2_size);
        info!("ConnectionMapping updated with upstream extranonce");
    }

    pub fn set_upstream_difficulty(&mut self, difficulty: f64) {
        self.upstream_difficulty = Some(difficulty);
        info!(
            "ConnectionMapping updated with upstream difficulty: {}",
            difficulty
        );
    }

    pub fn get_channels(&self) -> &HashMap<String, ConnectionInfo> {
        &self.downstream_channel_mapping
    }

    pub fn register_worker(&mut self, peer_addr: String, worker_name: String) {
        self.worker_to_peer.insert(worker_name, peer_addr);
    }

    pub fn get_peer_for_worker(&self, worker_name: &str) -> Option<&String> {
        self.worker_to_peer.get(worker_name)
    }

    pub fn get_channel_for_worker(&self, worker_name: &str) -> Option<&mpsc::Sender<String>> {
        self.get_peer_for_worker(worker_name)
            .and_then(|peer| self.downstream_channel_mapping.get(peer))
            .map(|info| &info.sender)
    }

    pub fn new_connection(
        &mut self,
        peer_addr: String,
        connection_id: u32,
        peer_msg_sender: mpsc::Sender<String>,
        control_tx: mpsc::Sender<ControlMsg>,
    ) {
        self.downstream_channel_mapping.insert(
            peer_addr,
            ConnectionInfo {
                connection_id,
                sender: peer_msg_sender,
                control_tx,
            },
        );
    }
}
