//! Swarm configuration constants.
//!
//! Centralizes all network configuration including boot nodes,
//! protocol parameters, and timing constants.

use libp2p::{core::multiaddr::Multiaddr, PeerId};
use std::time::Duration;

/// Boot node peer IDs for initial peer discovery.
pub const BOOTNODES: [&str; 1] = ["12D3KooWG9z8TziaNuYyEcc9FeUC3FTtrEf2XSnSdDpLvx4Jh2w3"];

/// DNS seed for boot node resolution.
pub const SEED_DNS: &str = "/dnsaddr/french.braidpool.net";

/// Combined address for DNS resolution and dialing boot nodes.
pub const BOOT_ADDR: &str =
    "/dnsaddr/french.braidpool.net/p2p/12D3KooWG9z8TziaNuYyEcc9FeUC3FTtrEf2XSnSdDpLvx4Jh2w3";

/// Latency smoothing factor for peer scoring (in seconds).
pub const LATENCY_ALPHA: u64 = 10;

/// Connection idle timeout (effectively infinite).
pub const IDLE_CONNECTION_TIMEOUT: Duration = Duration::from_secs(u64::MAX);

/// Default P2P port.
pub const DEFAULT_P2P_PORT: u16 = 6680;

/// Parses boot node configurations into peer IDs and addresses.
///
/// Returns a vector of (PeerId, Multiaddr) tuples for all valid boot nodes.
/// Invalid entries are logged and skipped.
pub fn parse_boot_nodes() -> Vec<(PeerId, Multiaddr)> {
    let mut result = Vec::new();

    for boot_peer in BOOTNODES {
        let peer_id = match boot_peer.parse::<PeerId>() {
            Ok(id) => id,
            Err(e) => {
                tracing::error!(
                    boot_peer = %boot_peer,
                    error = %e,
                    "Failed to parse boot peer ID, skipping"
                );
                continue;
            }
        };

        let seed_addr = match SEED_DNS.parse::<Multiaddr>() {
            Ok(addr) => addr,
            Err(e) => {
                tracing::error!(
                    seed_dns = %SEED_DNS,
                    error = %e,
                    "Failed to parse seed DNS, skipping"
                );
                continue;
            }
        };

        result.push((peer_id, seed_addr));
    }

    result
}

/// Parses the boot address for initial dialing.
pub fn parse_boot_addr() -> Result<Multiaddr, String> {
    BOOT_ADDR
        .parse()
        .map_err(|e| format!("Failed to parse boot address: {}", e))
}
