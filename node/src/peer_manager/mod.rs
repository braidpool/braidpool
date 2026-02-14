use crate::utils::BeadHash;
use libp2p::PeerId;
use serde_json::json;
use std::collections::{HashMap, HashSet};
use std::net::IpAddr;
use std::time::{Duration, Instant};

pub const IBD_BATCH_SIZE: usize = 500;
pub const MAX_IBD_RETRIES: u64 = 10;
/// Minimum number of peers required before initiating IBD
pub const MIN_PEERS_FOR_IBD: usize = 1;
/// Duration to wait before retrying IBD if no peers are available or all retries exhausted
pub const IBD_RETRY_DELAY: u64 = 20;
/// We wait for incoming beads with the range [current_timestamp,current_timestamp + MAX_IBD_INCOMING_THRESHOLD]
pub const MAX_IBD_INCOMING_THRESHOLD: u64 = 20;
/// Information about a peer in the network
#[derive(Debug, Clone)]
pub struct PeerInfo {
    /// The peer's ID
    pub peer_id: PeerId,
    /// The measured latency to the peer (from ping responses)
    pub latency: Option<Duration>,
    /// Whether this peer connection was initiated by the remote peer
    pub inbound: bool,
    /// When we last received a message from this peer
    pub last_message_time: Instant,
    /// Score used for peer ranking (higher is better)
    pub score: f64,
    /// Multiplier for score penalty, initially set to 0.01, doubles with each decrement
    pub score_penalty_multiplier: f64,
    /// Group identifier for geographic/network diversity (similar to Bitcoin's netgroup)
    pub geo_group: Option<String>,
    /// When we last sent a ping to this peer
    pub last_ping: Option<Instant>,
    /// Whether the peer is currently connected
    pub connected: bool,
    /// The peer's IP address
    pub ip_addr: Option<IpAddr>,
    /// Tracks the most recent tips received from each peer during IBD.
    /// (peer_id --> Vec<BeadHash>)
    ibd_peer_tips: Vec<BeadHash>,
    /// Tracks the current batch offset for each peer when requesting batched beads.
    /// (peer_id --> current offset)
    ibd_batch_offset: usize,
    /// Stores bead hashes obtained by GetBead requests from each peer.
    /// (peer_id --> Vec<BeadHash>)
    ibd_bead_queue: Vec<BeadHash>,
    ///Retry ibd count wrt each sync peer
    retry_count: u64,
}

impl PeerInfo {
    /// Create a new PeerInfo
    pub fn new(peer_id: PeerId, inbound: bool, ip: Option<IpAddr>) -> Self {
        Self {
            peer_id,
            latency: None,
            inbound,
            last_message_time: Instant::now(),
            score: 100.0,
            geo_group: ip.map(|addr| Self::calculate_geo_group(addr)),
            last_ping: None,
            connected: true,
            ip_addr: ip,
            score_penalty_multiplier: 0.01,
            ibd_batch_offset: IBD_BATCH_SIZE,
            ibd_peer_tips: Vec::new(),
            ibd_bead_queue: Vec::new(),
            retry_count: 0,
        }
    }

    /// Calculate a geographic group identifier from an IP address
    fn calculate_geo_group(ip: IpAddr) -> String {
        // This is a simplified implementation that just uses the first two octets
        // of an IPv4 address or the first 4 segments of an IPv6 address
        match ip {
            IpAddr::V4(ipv4) => {
                let octets = ipv4.octets();
                format!("v4-{}.{}", octets[0], octets[1])
            }
            IpAddr::V6(ipv6) => {
                let segments = ipv6.segments();
                format!("v6-{:x}:{:x}", segments[0], segments[1])
            }
        }
    }
}

/// Manager for peer connections and selection
pub struct PeerManager {
    /// Table of all known peers
    peers: HashMap<PeerId, PeerInfo>,
    /// Set of currently connected peers
    connected_peers: HashSet<PeerId>,
    /// Maximum number of peers to maintain
    max_peers: usize,
    /// Minimum acceptable peer score
    min_acceptable_score: f64,
    /// Score penalty for idle peers (per second)
    idle_penalty: f64,
    /// Score bonus for low-latency peers
    latency_bonus_factor: f64,
}

impl PeerManager {
    /// Create a new PeerManager
    pub fn new(max_peers: usize) -> Self {
        Self {
            peers: HashMap::new(),
            connected_peers: HashSet::new(),
            max_peers,
            min_acceptable_score: -100.0,
            idle_penalty: 0.1,
            latency_bonus_factor: 10.0,
        }
    }
    pub fn handle_update_and_fetch_batch_offset(
        &mut self,
        peer_id: PeerId,
        offset_sender: tokio::sync::oneshot::Sender<usize>,
        batch_size: usize,
    ) {
        if let Some(peer) = self.peers.get_mut(&peer_id) {
            let current_offset = peer.ibd_batch_offset.clone();
            match offset_sender.send(current_offset) {
                Ok(_) => {
                    tracing::info!("Sending newer offset and updating the current offset");
                    peer.ibd_batch_offset = peer.ibd_batch_offset + batch_size;
                }
                Err(error) => {
                    tracing::error!(error=?error, "Error while updating and sending it to request channel");
                }
            }
        } else {
            self.peers
                .insert(peer_id.clone(), PeerInfo::new(peer_id.clone(), false, None));
            match offset_sender.send(IBD_BATCH_SIZE) {
                Ok(_) => {
                    tracing::info!("Sent newly initialized offset to request channel");
                }
                Err(error) => {
                    tracing::error!(error=?error,"Error while initiating batch offset and sending it to request channel");
                }
            }
        }
    }

    pub fn handle_update_incoming(&mut self, peer_id: PeerId, data: Vec<BeadHash>) {
        if let Some(peer_info) = self.peers.get_mut(&peer_id) {
            peer_info.ibd_bead_queue.extend(data.into_iter());
        } else {
            tracing::error!("PeerInfo not found while updating incoming beads");
        }
    }

    pub fn handle_update_ibd_peer_tips(&mut self, peer_id: PeerId, tips: Vec<BeadHash>) {
        if let Some(peer_info) = self.peers.get_mut(&peer_id) {
            peer_info.ibd_peer_tips.extend(tips.into_iter());
        } else {
            tracing::error!("PeerInfo not found while updating Tips mappping");
        }
    }

    pub fn handle_fetch_tips(
        &mut self,
        peer_id: PeerId,
        sender: tokio::sync::oneshot::Sender<Vec<BeadHash>>,
    ) {
        if let Some(peer_info) = self.peers.get_mut(&peer_id) {
            let cached = peer_info.ibd_peer_tips.clone();
            match sender.send(cached.clone()) {
                Ok(_) => tracing::info!("Cached tips sent successfully to swarm event loop"),
                Err(error) => tracing::error!(error=?error,"Tips not sent"),
            }
        } else {
            tracing::error!("PeerInfo not found while sending Tips mappping");
        }
    }

    pub fn handle_fetch_ibd_bead_queue(
        &mut self,
        peer_id: PeerId,
        sender: tokio::sync::oneshot::Sender<Vec<BeadHash>>,
    ) {
        if let Some(peer_info) = self.peers.get_mut(&peer_id) {
            let cached = peer_info.ibd_bead_queue.clone();
            match sender.send(cached.clone()) {
                Ok(_) => {
                    tracing::info!("Cached get bead hashes sent successfully to swarm event loop")
                }
                Err(error) => tracing::error!(error=?error,"Beadhashes not sent"),
            }
        } else {
            tracing::error!("PeerInfo not found while fetching GetBead mappping");
        }
    }

    pub fn handle_get_incoming_bead_retry_count(
        &mut self,
        peer_id: PeerId,
        sender: tokio::sync::oneshot::Sender<u64>,
    ) {
        if let Some(peer_info) = self.peers.get_mut(&peer_id) {
            let retries = peer_info.retry_count;
            match sender.send(retries) {
                Ok(_) => tracing::info!("Retry count sent successfully to swarm event loop"),
                Err(_) => tracing::error!("Retry count not sent"),
            }
        } else {
            tracing::error!("PeerInfo not found while fetching retry count");
        }
    }

    pub fn handle_update_retry_count(&mut self, peer_id: PeerId) {
        if let Some(peer_info) = self.peers.get_mut(&peer_id) {
            peer_info.retry_count += 1;
            tracing::info!(peer_id=?peer_id,"Incremented retry count to {}",peer_info.retry_count);
        } else {
            tracing::error!("PeerInfo not found while updating retry count");
        }
    }
    /// Add a new peer or update an existing one
    pub fn add_peer(&mut self, peer_id: PeerId, inbound: bool, ip: Option<IpAddr>) {
        if let Some(peer) = self.peers.get_mut(&peer_id) {
            // Update existing peer
            peer.connected = true;
            peer.inbound = inbound;
            if let Some(ip_addr) = ip {
                peer.ip_addr = Some(ip_addr);
                peer.geo_group = Some(PeerInfo::calculate_geo_group(ip_addr));
            }
            peer.last_message_time = Instant::now();
        } else {
            // Add new peer
            let peer_info = PeerInfo::new(peer_id, inbound, ip);
            self.peers.insert(peer_id, peer_info);
        }
        self.connected_peers.insert(peer_id);
    }

    /// Remove a peer
    pub fn remove_peer(&mut self, peer_id: &PeerId) {
        if let Some(peer) = self.peers.get_mut(peer_id) {
            peer.connected = false;
        }
        self.connected_peers.remove(peer_id);
    }

    /// Update the latency measurement for a peer
    pub fn update_latency(&mut self, peer_id: &PeerId, rtt: Duration) {
        if let Some(peer) = self.peers.get_mut(peer_id) {
            peer.latency = Some(rtt);

            // Adjust score based on latency - lower latency gives higher score
            let latency_ms = rtt.as_millis() as f64;
            if latency_ms > 0.0 {
                // Bonus for low-latency peers, penalty for high-latency ones
                let latency_score = self.latency_bonus_factor / latency_ms;
                peer.score += latency_score;
            }

            peer.last_ping = Some(Instant::now());
        }
    }

    /// Mark that we received a message from a peer
    pub fn mark_message(&mut self, peer_id: &PeerId) {
        if let Some(peer) = self.peers.get_mut(peer_id) {
            peer.last_message_time = Instant::now();

            // Small bonus for activity
            self.update_score(peer_id, 0.5);
        }
    }

    /// Update a peer's score
    pub fn update_score(&mut self, peer_id: &PeerId, delta: f64) {
        if let Some(peer) = self.peers.get_mut(peer_id) {
            peer.score += delta;
        }
    }

    /// Get the top k peers for message propagation with network diversity
    pub fn get_top_k_peers_for_propagation(&self, k: usize) -> Vec<PeerId> {
        if k == 0 || self.connected_peers.is_empty() {
            return Vec::new();
        }

        // Create a list of connected peers with their info
        let mut peer_list: Vec<(&PeerId, &PeerInfo)> = self
            .peers
            .iter()
            .filter(|(id, info)| self.connected_peers.contains(id) && info.connected)
            .collect();

        // Sort by score (highest first)
        peer_list.sort_by(|a, b| {
            b.1.score
                .partial_cmp(&a.1.score)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        // Select peers with network diversity
        let mut selected = Vec::with_capacity(k);
        let mut selected_groups = HashSet::new();

        // First pass: select one peer from each geo_group
        for (id, info) in &peer_list {
            if selected.len() >= k {
                break;
            }

            if let Some(group) = &info.geo_group {
                if !selected_groups.contains(group) {
                    selected.push(**id);
                    selected_groups.insert(group.clone());
                }
            } else {
                // If no geo_group, just add the peer
                selected.push(**id);
            }
        }

        // Second pass: fill remaining slots with highest-scoring peers not yet selected
        if selected.len() < k {
            for (id, _) in &peer_list {
                if selected.len() >= k {
                    break;
                }

                if !selected.contains(id) {
                    selected.push(**id);
                }
            }
        }

        selected
    }

    /// Get candidates for eviction (low score, high latency, or stale)
    pub fn get_eviction_candidates(&self) -> Vec<PeerId> {
        let now = Instant::now();
        let mut candidates = Vec::new();

        for (id, info) in &self.peers {
            if !info.connected {
                continue;
            }

            // Check for very low score
            if info.score < self.min_acceptable_score {
                candidates.push(*id);
                continue;
            }

            // Check for very high latency
            if let Some(latency) = info.latency {
                if latency > Duration::from_secs(2) {
                    candidates.push(*id);
                    continue;
                }
            }

            // Check for staleness (no messages for a long time)
            let idle_time = now.duration_since(info.last_message_time);
            if idle_time > Duration::from_secs(300) {
                // 5 minutes
                candidates.push(*id);
            }
        }

        // Sort by score (lowest first)
        candidates.sort_by(|a, b| {
            let score_a = self.peers.get(a).map_or(0.0, |p| p.score);
            let score_b = self.peers.get(b).map_or(0.0, |p| p.score);
            score_a
                .partial_cmp(&score_b)
                .unwrap_or(std::cmp::Ordering::Equal)
        });

        candidates
    }

    /// Get the number of connected peers
    pub fn num_connected_peers(&self) -> usize {
        self.connected_peers.len()
    }

    /// Get peer information as JSON value for RPC responses
    pub fn get_peers_json(&self) -> serde_json::Value {
        let total_peers = self.peers.len();
        let mut avg_latency_ms = 0.0;
        let mut latency_count = 0;
        let mut geo_groups = HashSet::new();
        let mut inbound_count = 0;
        let now = Instant::now();
        let mut peers_json_array: Vec<serde_json::Value> = Vec::new();

        for info in self.peers.values().filter(|p| p.connected) {
            if info.inbound {
                inbound_count += 1;
            }
            if let Some(latency) = info.latency {
                avg_latency_ms += latency.as_millis() as f64;
                latency_count += 1;
            }
            if let Some(group) = &info.geo_group {
                geo_groups.insert(group.clone());
            }

            let last_seen_secs = now.duration_since(info.last_message_time).as_secs();
            peers_json_array.push(json!({
                "peer_id": info.peer_id.to_base58(),
                "ip": info.ip_addr.map(|ip| ip.to_string()),
                "inbound": info.inbound,
                "latency_ms": info.latency.map(|l| l.as_millis() as f64),
                "score": info.score,
                "last_seen_secs": last_seen_secs,
                "geo_group": info.geo_group,
            }));
        }

        if latency_count > 0 {
            avg_latency_ms /= latency_count as f64;
        }

        let connected = peers_json_array.len();

        json!({
            "total_peers": total_peers,
            "connected": connected,
            "inbound": inbound_count,
            "outbound": connected - inbound_count,
            "network_groups": geo_groups.len(),
            "avg_latency_ms": avg_latency_ms,
            "peers": peers_json_array,
        })
    }

    /// Get a summary of peer statistics
    pub fn peer_stats_summary(&self) -> String {
        let total_peers = self.peers.len();
        let connected = self.connected_peers.len();

        let mut inbound = 0;
        let mut outbound = 0;
        let mut avg_latency_ms = 0.0;
        let mut latency_count = 0;
        let mut geo_groups = HashSet::new();

        for info in self.peers.values() {
            if !info.connected {
                continue;
            }

            if info.inbound {
                inbound += 1;
            } else {
                outbound += 1;
            }

            if let Some(latency) = info.latency {
                avg_latency_ms += latency.as_millis() as f64;
                latency_count += 1;
            }

            if let Some(group) = &info.geo_group {
                geo_groups.insert(group.clone());
            }
        }

        if latency_count > 0 {
            avg_latency_ms /= latency_count as f64;
        }

        format!(
            "Peers: {}/{} connected ({} inbound, {} outbound), {} network groups, {:.2}ms avg latency",
            connected, total_peers, inbound, outbound, geo_groups.len(), avg_latency_ms
        )
    }

    /// Periodic maintenance task to update peer scores and evict peers if needed
    pub fn maintenance(&mut self) {
        let now = Instant::now();

        // Update scores based on idle time
        for (_id, info) in self.peers.iter_mut() {
            if !info.connected {
                continue;
            }

            let idle_time = now.duration_since(info.last_message_time);
            let idle_seconds = idle_time.as_secs() as f64;

            // Apply idle penalty
            let penalty = idle_seconds * self.idle_penalty;
            info.score -= penalty;
        }

        // Evict peers if we're over the limit
        if self.connected_peers.len() > self.max_peers {
            let to_evict = self.get_eviction_candidates();
            let num_to_evict = self.connected_peers.len() - self.max_peers;

            for id in to_evict.iter().take(num_to_evict) {
                self.remove_peer(id);
            }
        }
    }

    /// Update the peer's score due to an invalid bead from the peer
    pub fn penalize_for_invalid_bead(&mut self, peer_id: &PeerId) {
        if let Some(peer) = self.peers.get_mut(peer_id) {
            // Apply a penalty to the peer's score for sending an invalid bead
            peer.score -= peer.score * peer.score_penalty_multiplier;
            peer.score_penalty_multiplier *= 2.0; // Double the penalty multiplier
            peer.last_message_time = Instant::now(); // Reset last message time
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use libp2p::identity::Keypair;
    use std::net::{Ipv4Addr, Ipv6Addr};

    fn generate_peer_id() -> PeerId {
        let keypair = Keypair::generate_ed25519();
        PeerId::from(keypair.public())
    }

    #[test]
    fn test_add_remove_peer() {
        let mut manager = PeerManager::new(10);
        let peer_id = generate_peer_id();
        let ip = Some(IpAddr::V4(Ipv4Addr::new(192, 168, 1, 1)));

        manager.add_peer(peer_id, false, ip);
        assert_eq!(manager.num_connected_peers(), 1);

        manager.remove_peer(&peer_id);
        assert_eq!(manager.num_connected_peers(), 0);
    }

    #[test]
    fn test_geo_group_calculation() {
        let ipv4 = IpAddr::V4(Ipv4Addr::new(192, 168, 1, 1));
        let ipv6 = IpAddr::V6(Ipv6Addr::new(0x2001, 0xdb8, 0, 0, 0, 0, 0, 1));

        assert_eq!(PeerInfo::calculate_geo_group(ipv4), "v4-192.168");
        assert_eq!(PeerInfo::calculate_geo_group(ipv6), "v6-2001:db8");
    }

    #[test]
    fn test_peer_propagation_selection() {
        let mut manager = PeerManager::new(10);

        // Add peers with different geo groups
        let peer1 = generate_peer_id();
        let peer2 = generate_peer_id();
        let peer3 = generate_peer_id();

        manager.add_peer(
            peer1,
            false,
            Some(IpAddr::V4(Ipv4Addr::new(192, 168, 1, 1))),
        );
        manager.add_peer(
            peer2,
            false,
            Some(IpAddr::V4(Ipv4Addr::new(192, 168, 2, 1))),
        );
        manager.add_peer(peer3, false, Some(IpAddr::V4(Ipv4Addr::new(10, 0, 1, 1))));

        // Update scores
        manager.update_score(&peer1, 10.0);
        manager.update_score(&peer2, 5.0);
        manager.update_score(&peer3, 15.0);

        // Get top 2 peers for propagation
        let top_peers = manager.get_top_k_peers_for_propagation(2);
        assert_eq!(top_peers.len(), 2);

        // Should select peer3 (highest score) and either peer1 or peer2 (different geo group)
        assert!(top_peers.contains(&peer3));
    }
}
