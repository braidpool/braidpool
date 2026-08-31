use libp2p::core::multiaddr::Protocol;
use libp2p::{Multiaddr, PeerId};
use serde_json::json;
use std::collections::{HashMap, HashSet};
use std::net::IpAddr;
use std::time::{Duration, Instant};

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

/// A connection that has been established but whose protocol negotiation has
/// not yet completed.
///
/// Braidpool scopes its libp2p protocol IDs by network, so a peer on a different
/// network can still open a transport connection but will fail to negotiate any
/// substream. Connections are parked here until the Identify exchange proves the
/// peer speaks this node's protocols, and only then promoted into `peers` - which
/// keeps foreign-network peers out of peer selection and scoring entirely.
#[derive(Debug, Clone)]
pub struct PendingPeer {
    /// Remote address the connection was established on
    pub remote_addr: Multiaddr,
    /// Whether the local node dialed the peer, rather than being dialed by it
    pub is_dialer: bool,
}

impl PendingPeer {
    /// Extracts the peer's IP address from its remote multiaddr, if it has one.
    ///
    /// # Returns
    /// The first `Ip4`/`Ip6` component of the address, or `None` for addresses
    /// that carry no literal IP (a DNS multiaddr, for example).
    pub fn remote_ip(&self) -> Option<IpAddr> {
        self.remote_addr.iter().find_map(|p| match p {
            Protocol::Ip4(ip) => Some(IpAddr::V4(ip)),
            Protocol::Ip6(ip) => Some(IpAddr::V6(ip)),
            _ => None,
        })
    }
}

/// Manager for peer connections and selection
pub struct PeerManager {
    /// Table of all known peers
    peers: HashMap<PeerId, PeerInfo>,
    /// Set of currently connected peers
    connected_peers: HashSet<PeerId>,
    /// Connections established but not yet cleared by protocol negotiation
    pending_peers: HashMap<PeerId, PendingPeer>,
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
            pending_peers: HashMap::new(),
            max_peers,
            min_acceptable_score: -100.0,
            idle_penalty: 0.1,
            latency_bonus_factor: 10.0,
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
    ///
    /// Also discards any pending entry for `peer_id`, so a connection that drops
    /// before protocol negotiation completes leaves nothing behind.
    pub fn remove_peer(&mut self, peer_id: &PeerId) {
        if let Some(peer) = self.peers.get_mut(peer_id) {
            peer.connected = false;
        }
        self.connected_peers.remove(peer_id);
        self.pending_peers.remove(peer_id);
    }

    /// Records a freshly established connection awaiting protocol negotiation.
    ///
    /// The peer takes no part in propagation or scoring until
    /// [`PeerManager::promote_pending_peer`] accepts it.
    ///
    /// # Arguments
    /// * `peer_id` - The peer that connected
    /// * `remote_addr` - Address the connection was established on
    /// * `is_dialer` - Whether the local node dialed the peer
    pub fn add_pending_peer(&mut self, peer_id: PeerId, remote_addr: Multiaddr, is_dialer: bool) {
        self.pending_peers.insert(
            peer_id,
            PendingPeer {
                remote_addr,
                is_dialer,
            },
        );
    }

    /// Discards a pending connection that failed protocol negotiation.
    ///
    /// # Arguments
    /// * `peer_id` - The peer to discard
    ///
    /// # Returns
    /// The discarded entry, or `None` if the peer was not pending.
    pub fn drop_pending_peer(&mut self, peer_id: &PeerId) -> Option<PendingPeer> {
        self.pending_peers.remove(peer_id)
    }

    /// Promotes a pending connection into a tracked peer after its protocol
    /// negotiation succeeded.
    ///
    /// The peer's IP is taken from the address the connection was established on,
    /// and `inbound` from whether the remote dialed us.
    ///
    /// # Arguments
    /// * `peer_id` - The peer to promote
    ///
    /// # Returns
    /// `true` if a pending entry existed and was promoted, `false` otherwise -
    /// a `false` return means the connection closed before Identify completed.
    pub fn promote_pending_peer(&mut self, peer_id: &PeerId) -> bool {
        let Some(pending) = self.pending_peers.remove(peer_id) else {
            return false;
        };
        let ip = pending.remote_ip();
        self.add_peer(*peer_id, !pending.is_dialer, ip);
        true
    }

    /// Returns the number of connections awaiting protocol negotiation.
    pub fn num_pending_peers(&self) -> usize {
        self.pending_peers.len()
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

    fn test_multiaddr(s: &str) -> Multiaddr {
        s.parse().expect("valid multiaddr literal")
    }

    #[test]
    fn pending_peer_is_not_connected_until_promoted() {
        let mut manager = PeerManager::new(10);
        let peer_id = generate_peer_id();

        manager.add_pending_peer(
            peer_id,
            test_multiaddr("/ip4/74.50.123.158/udp/6680/quic-v1"),
            false,
        );
        // A peer awaiting protocol negotiation takes no part in peer selection.
        assert_eq!(manager.num_pending_peers(), 1);
        assert_eq!(manager.num_connected_peers(), 0);
        assert!(manager.get_top_k_peers_for_propagation(5).is_empty());

        assert!(manager.promote_pending_peer(&peer_id));
        assert_eq!(manager.num_pending_peers(), 0);
        assert_eq!(manager.num_connected_peers(), 1);
    }

    #[test]
    fn promoting_records_ip_and_inbound_from_the_connection() {
        let mut manager = PeerManager::new(10);
        let inbound_peer = generate_peer_id();
        let outbound_peer = generate_peer_id();

        // is_dialer == false means the remote dialed us, so the peer is inbound.
        manager.add_pending_peer(
            inbound_peer,
            test_multiaddr("/ip4/74.50.123.158/udp/6680/quic-v1"),
            false,
        );
        manager.add_pending_peer(
            outbound_peer,
            test_multiaddr("/ip6/2001:4860:4860::8888/udp/6680/quic-v1"),
            true,
        );
        assert!(manager.promote_pending_peer(&inbound_peer));
        assert!(manager.promote_pending_peer(&outbound_peer));

        let inbound = manager.peers.get(&inbound_peer).unwrap();
        assert!(inbound.inbound);
        assert_eq!(
            inbound.ip_addr,
            Some(IpAddr::V4(Ipv4Addr::new(74, 50, 123, 158)))
        );

        let outbound = manager.peers.get(&outbound_peer).unwrap();
        assert!(!outbound.inbound);
        assert_eq!(
            outbound.ip_addr,
            Some(IpAddr::V6(Ipv6Addr::new(
                0x2001, 0x4860, 0x4860, 0, 0, 0, 0, 0x8888
            )))
        );
    }

    #[test]
    fn failed_negotiation_drops_the_pending_peer() {
        let mut manager = PeerManager::new(10);
        let peer_id = generate_peer_id();

        manager.add_pending_peer(
            peer_id,
            test_multiaddr("/ip4/74.50.123.158/udp/6680/quic-v1"),
            true,
        );
        let dropped = manager.drop_pending_peer(&peer_id);
        assert!(dropped.is_some());
        assert!(dropped.unwrap().is_dialer);
        assert_eq!(manager.num_pending_peers(), 0);

        // A peer that never negotiated must not be promotable afterwards.
        assert!(!manager.promote_pending_peer(&peer_id));
        assert_eq!(manager.num_connected_peers(), 0);
    }

    #[test]
    fn closing_a_connection_clears_its_pending_entry() {
        let mut manager = PeerManager::new(10);
        let peer_id = generate_peer_id();

        manager.add_pending_peer(
            peer_id,
            test_multiaddr("/ip4/74.50.123.158/udp/6680/quic-v1"),
            false,
        );
        manager.remove_peer(&peer_id);
        assert_eq!(manager.num_pending_peers(), 0);
        assert!(!manager.promote_pending_peer(&peer_id));
    }

    #[test]
    fn pending_peer_without_literal_ip_has_no_ip() {
        let pending = PendingPeer {
            remote_addr: test_multiaddr("/dns4/example.com/udp/6680/quic-v1"),
            is_dialer: true,
        };
        assert_eq!(pending.remote_ip(), None);
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
