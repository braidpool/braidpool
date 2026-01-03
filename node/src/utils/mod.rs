// Bitcoin Imports
use crate::{
    bead::Bead,
    committed_metadata::{CommittedMetadata, TimeVec, TxIdVec},
    error::StratumErrors,
    uncommitted_metadata::UnCommittedMetadata,
};
use ::bitcoin::BlockHash;
use bitcoin::{
    absolute::MedianTimePast as Time, ecdsa::Signature, BlockHeader, BlockTime, BlockVersion,
    CompactTarget, EcdsaSighashType, TxMerkleNode,
};
// Standard Imports
#[allow(unused_imports)]
use tracing::{debug, error, info, trace, warn};

pub mod test_utils;

// External Type Aliases
pub type BeadHash = BlockHash;
pub type Byte = u8;
pub type Bytes = Vec<Byte>;

// Internal Type Aliases
#[allow(dead_code)]
pub(crate) type Relatives = HashSet<BeadHash>;

// Error Definitions
use std::{collections::HashSet, net::IpAddr, str::FromStr};

pub(crate) fn hashset_to_vec_deterministic(hashset: &HashSet<BeadHash>) -> Vec<BeadHash> {
    let mut vec: Vec<BeadHash> = hashset.iter().cloned().collect();
    vec.sort();
    vec
}

pub(crate) fn vec_to_hashset(vec: Vec<BeadHash>) -> HashSet<BeadHash> {
    vec.iter().cloned().collect()
}

/// Get list of actual local IPv4 addresses for servers binding to 0.0.0.0
///
/// Returns all IPv4 addresses found on network interfaces.
/// Returns empty vector if no interfaces found or on error.
pub fn get_local_ipv4_addresses() -> Vec<IpAddr> {
    if_addrs::get_if_addrs()
        .unwrap_or_default()
        .into_iter()
        .filter_map(|iface| {
            if let if_addrs::IfAddr::V4(ref addr) = iface.addr {
                Some(IpAddr::V4(addr.ip))
            } else {
                None
            }
        })
        .collect()
}

/// Log server listening endpoints with actual IP addresses
///
/// When binding to 0.0.0.0, this enumerates all non-loopback IPv4 interfaces
/// and return each available endpoint. Otherwise, logs the configured address.
///
/// # Arguments
/// * `bind_host` - The configured hostname (e.g., "0.0.0.0", "127.0.0.1", or specific IP)
/// * `port` - The port number the server is listening on
/// * `protocol` - Protocol prefix for the URL (e.g., "stratum+tcp", "http")
pub fn server_endpoints(bind_host: &str, port: u16, protocol: &str) -> Vec<String> {
    if bind_host == "0.0.0.0" {
        let local_ips = get_local_ipv4_addresses();
        if local_ips.is_empty() {
            Vec::new()
        } else {
            local_ips
                .into_iter()
                .map(|ip| format!("{}://{}:{}", protocol, ip, port))
                .collect()
        }
    } else {
        vec![format!("{}://{}:{}", protocol, bind_host, port)]
    }
}
#[allow(unused)]
/// Use bitcoin mainnet max attainable target to convert the hash into difficulty
/// This global difficulty to used to track difficult adjustment by the pool, independent of the chain that is being mined.
pub fn get_true_difficulty(
    hash: &bitcoin::BlockHash,
    configured_network: bitcoin::Network,
) -> u128 {
    let mut bytes = hash.to_byte_array();
    bytes.reverse();
    let diff = u128::from_str_radix(&hex::encode(&bytes[..16]), 16).unwrap();
    let bead_diff = match configured_network {
        bitcoin::Network::Bitcoin
        | bitcoin::Network::Testnet(bitcoin::TestnetVersion::V4)
        | bitcoin::Network::CPUNet => (0xFFFF_u128 << (208 - 128)) / diff,
        bitcoin::Network::Regtest => 0x7FFF_FF00u128 << 96 / diff,
        bitcoin::Network::Signet => 0x0377_ae00 << 80 / diff,
        _ => 0x0377_ae00 << 80 / diff,
    };
    return bead_diff;
}
//Validation for usernames and parsing the payout_address for the downstream connected
pub fn validate(
    username: &str,
    network: bitcoin::Network,
) -> Result<(&str, Option<&str>), StratumErrors> {
    let parts: Vec<&str> = username.splitn(2, '.').collect();
    let address_part = parts[0];
    let address = address_part.parse::<bitcoin::Address<_>>().map_err(|_e| {
        StratumErrors::UserNameParseError {
            error: crate::error::UsernameValidationError::InvalidAddress {
                address: address_part.to_string(),
            },
        }
    })?;

    address
        .require_network(network)
        .map_err(|_| StratumErrors::UserNameParseError {
            error: crate::error::UsernameValidationError::NetworkIncompatibleAddress {
                network: network.to_string(),
            },
        })?;

    // Extract worker name if present
    if parts.len() > 1 {
        Ok((address_part, Some(parts[1])))
    } else {
        Ok((address_part, None))
    }
}
// Helper function to create test beads
pub fn create_test_bead(nonce: u32, prev_hash: Option<BlockHash>) -> Bead {
    let public_key = "020202020202020202020202020202020202020202020202020202020202020202"
        .parse::<bitcoin::PublicKey>()
        .unwrap();
    let time_hash_set = TimeVec(Vec::new());
    let mut parent_hash_set: HashSet<BlockHash> = HashSet::new();
    if let Some(hash) = prev_hash {
        parent_hash_set.insert(hash);
    }
    let weak_target = CompactTarget::from_consensus(486604799);
    let min_target = CompactTarget::from_consensus(486604799);
    let time_val = Time::from_consensus(1653195600).unwrap();
    let test_committed_metadata: CommittedMetadata = CommittedMetadata {
        comm_pub_key: public_key,
        min_target: min_target,
        miner_ip: "".to_string(),
        transaction_ids: TxIdVec(vec![]),
        parents: parent_hash_set,
        parent_bead_timestamps: time_hash_set,
        payout_address: String::from(""),
        start_timestamp: time_val,
        weak_target: weak_target,
    };
    let extra_nonce_1 = 42;
    let extra_nonce_2 = rand::random::<u32>();

    let hex = "3046022100839c1fbc5304de944f697c9f4b1d01d1faeba32d751c0f7acb21ac8a0f436a72022100e89bd46bb3a5a62adc679f659b7ce876d83ee297c7a5587b2011c4fcc72eab45";
    let sig = Signature {
        signature: secp256k1::ecdsa::Signature::from_str(hex).unwrap(),
        sighash_type: EcdsaSighashType::All,
    };
    let test_uncommitted_metadata = UnCommittedMetadata {
        broadcast_timestamp: time_val,
        extra_nonce_1: extra_nonce_1,
        extra_nonce_2: extra_nonce_2,
        signature: sig,
    };
    let test_bytes: [u8; 32] = [0u8; 32];
    let test_block_header = BlockHeader {
        version: BlockVersion::TWO,
        prev_blockhash: prev_hash.unwrap_or(BlockHash::from_byte_array(test_bytes)),
        bits: CompactTarget::from_consensus(486604799),
        nonce: nonce,
        time: BlockTime::from_u32(8328429),
        merkle_root: TxMerkleNode::from_byte_array(test_bytes),
    };
    Bead {
        block_header: test_block_header,
        committed_metadata: test_committed_metadata,
        uncommitted_metadata: test_uncommitted_metadata,
    }
}

#[cfg(test)]
mod tests {
    use bitcoin::Network;

    use crate::error::UsernameValidationError;

    use super::*;
    #[test]
    fn server_endpoints_returns_single_endpoint_for_specific_host() {
        let result = server_endpoints("127.0.0.1", 8080, "http");
        assert_eq!(result, vec!["http://127.0.0.1:8080"]);
    }

    #[test]
    fn server_endpoints_expands_all_interfaces_when_ips_provided() {
        let local_ips = get_local_ipv4_addresses();
        if local_ips.is_empty() {
            // Some CI sandboxes may report no interfaces; in that case ensure the function returns empty too.
            let result = server_endpoints("0.0.0.0", 3333, "stratum+tcp");
            assert!(result.is_empty());
        } else {
            let expected: Vec<String> = local_ips
                .into_iter()
                .map(|ip| format!("stratum+tcp://{}:3333", ip))
                .collect();
            let result = server_endpoints("0.0.0.0", 3333, "stratum+tcp");
            assert_eq!(result, expected);
        }
    }
    #[test]
    fn valid_address_with_worker() {
        let username = "bc1qpa77defz30uavu8lxef98q95rae6m7t8au9vp7.worker1";
        let result = validate(username, Network::Bitcoin);

        assert!(result.is_ok());

        let (address, worker) = result.unwrap();
        assert_eq!(address, "bc1qpa77defz30uavu8lxef98q95rae6m7t8au9vp7");
        assert_eq!(worker, Some("worker1"));
    }

    #[test]
    fn invalid_bitcoin_address() {
        let username = "not_a_valid_address.worker";
        let result = validate(username, Network::Bitcoin);

        assert!(result.is_err());

        match result {
            Err(StratumErrors::UserNameParseError { error }) => {
                assert_eq!(
                    error,
                    UsernameValidationError::InvalidAddress {
                        address: "not_a_valid_address".to_string()
                    }
                )
            }
            _ => panic!("Expected UserNameParseError for invalid address"),
        }
    }

    #[test]
    fn network_incompatible_address() {
        // Mainnet address checked against Testnet
        let username = "bc1qpa77defz30uavu8lxef98q95rae6m7t8au9vp7";
        let result = validate(username, Network::Testnet(bitcoin::TestnetVersion::V4));

        assert!(result.is_err());

        match result {
            Err(StratumErrors::UserNameParseError { error }) => {
                assert_eq!(
                    error,
                    UsernameValidationError::NetworkIncompatibleAddress {
                        network: "testnet4".to_string()
                    }
                )
            }
            _ => panic!("Expected UserNameParseError for network mismatch"),
        }
    }
}
