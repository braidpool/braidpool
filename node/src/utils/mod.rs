// Bitcoin Imports
use crate::config::PoolNetwork;
use crate::{
    bead::Bead,
    committed_metadata::{CommittedMetadata, TimeVec, TxIdVec},
    uncommitted_metadata::UnCommittedMetadata,
};
use ::bitcoin::BlockHash;
use bitcoin::{
    absolute::Time,
    block::{Header as BlockHeader, Version as BlockVersion},
    ecdsa::Signature,
    hashes::Hash,
    secp256k1, CompactTarget, EcdsaSighashType, TxMerkleNode,
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
use std::{
    collections::HashSet,
    fs,
    io::ErrorKind,
    net::IpAddr,
    path::{Path, PathBuf},
    str::FromStr,
};
/// Computes a bead's block hash under the rules of `network`.
pub fn compute_block_hash(block_header: &BlockHeader, network: PoolNetwork) -> BlockHash {
    network.block_hash(block_header)
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
/// Resolves the node's data directory, creating it if it does not exist yet.
pub fn resolve_datadir(datadir: &Path) -> std::io::Result<PathBuf> {
    let datadir_str = datadir.to_str().ok_or_else(|| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            "Invalid datadir path encoding",
        )
    })?;
    let expanded = shellexpand::full(datadir_str).map_err(|e| {
        std::io::Error::new(
            std::io::ErrorKind::InvalidInput,
            format!("Shell expansion failed: {}", e),
        )
    })?;
    let datadir_path = PathBuf::from(&*expanded);

    match fs::metadata(&datadir_path) {
        Ok(metadata) => {
            if !metadata.is_dir() {
                return Err(std::io::Error::new(
                    std::io::ErrorKind::InvalidInput,
                    format!(
                        "Data directory exists but is not a directory: {}",
                        datadir_path.display()
                    ),
                ));
            }
            info!(datadir = %datadir_path.display(), "Using existing data directory");
        }

        Err(error) if error.kind() == ErrorKind::NotFound => {
            info!(datadir = %datadir_path.display(), "Creating new data directory");
            fs::create_dir_all(&datadir_path)?;
        }
        Err(error) => {
            error!(
                datadir = %datadir_path.display(),
                error = %error,
                "Failed to read data directory metadata"
            );
            return Err(error);
        }
    }

    Ok(datadir_path)
}

/// Easiest compact target: exponent `0x20`, mantissa `0x7fffff`.
///
/// About half of all header hashes meet it, so test beads can grind a nonce
/// in a few increments.
pub(crate) const EASIEST_COMPACT_TARGET: u32 = 0x207fffff;

/// `start_timestamp` shared by every test bead, so fixtures stay deterministic
/// and a child can copy its parents' timestamps without looking them up.
pub(crate) const TEST_START_TIMESTAMP: u32 = 1653195600;

/// Increments `header.nonce`, starting from its current value, until the header
/// hash meets `header.bits` under `network`.
///
/// The search stops if every nonce has been tried. [`EASIEST_COMPACT_TARGET`]
/// is met long before that happens.
pub(crate) fn grind_test_header(header: &mut BlockHeader, network: PoolNetwork) {
    let target = bitcoin::Target::from_compact(header.bits);
    let start = header.nonce;
    loop {
        if target.is_met_by(network.block_hash(header)) {
            return;
        }
        header.nonce = header.nonce.wrapping_add(1);
        if header.nonce == start {
            return;
        }
    }
}

/// Builds a test bead whose header meets [`EASIEST_COMPACT_TARGET`] on cpunet.
///
/// `nonce` is the first nonce tried. It is also mixed into the merkle root so
/// two beads that share `prev_hash` stay distinct after grinding. When
/// `prev_hash` is set it is the sole parent, with one matching parent timestamp.
/// The payout address is a valid cpunet address.
pub fn create_test_bead(nonce: u32, prev_hash: Option<BlockHash>) -> Bead {
    let public_key = "020202020202020202020202020202020202020202020202020202020202020202"
        .parse::<bitcoin::PublicKey>()
        .unwrap();
    let mut parent_hash_set: Vec<BlockHash> = Vec::new();
    if let Some(hash) = prev_hash {
        parent_hash_set.push(hash);
    }
    let weak_target = CompactTarget::from_consensus(486604799);
    let min_target = CompactTarget::from_consensus(486604799);
    let time_val = Time::from_consensus(TEST_START_TIMESTAMP).unwrap();
    let parent_bead_timestamps = if prev_hash.is_some() {
        TimeVec(vec![time_val])
    } else {
        TimeVec(Vec::new())
    };
    let payout_address =
        crate::config::CoinbaseConfig::from_network(PoolNetwork::Cpunet).pool_payout_address;
    let test_committed_metadata: CommittedMetadata = CommittedMetadata {
        comm_pub_key: public_key,
        min_target: min_target,
        miner_ip: "".to_string(),
        transaction_ids: TxIdVec(vec![]),
        parents: parent_hash_set,
        parent_bead_timestamps,
        payout_address,
        start_timestamp: time_val,
        weak_target: weak_target,
    };
    let extra_nonce_1 = rand::random::<u64>();
    let extra_nonce_2 = rand::random::<u64>();

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
    let mut merkle_bytes: [u8; 32] = [0u8; 32];
    merkle_bytes[..4].copy_from_slice(&nonce.to_le_bytes());
    let mut test_block_header = BlockHeader {
        version: BlockVersion::TWO,
        prev_blockhash: prev_hash.unwrap_or(BlockHash::from_byte_array([0u8; 32])),
        bits: CompactTarget::from_consensus(EASIEST_COMPACT_TARGET),
        nonce,
        time: 8328429,
        merkle_root: TxMerkleNode::from_byte_array(merkle_bytes),
    };
    grind_test_header(&mut test_block_header, PoolNetwork::Cpunet);
    Bead {
        block_header: test_block_header,
        committed_metadata: test_committed_metadata,
        uncommitted_metadata: test_uncommitted_metadata,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn unique_temp_test_path(label: &str) -> PathBuf {
        let suffix = rand::random::<u8>();
        std::env::temp_dir().join(format!(
            "braidpool-test-{}-{}-{:02x}",
            label,
            std::process::id(),
            suffix
        ))
    }

    #[test]
    fn resolve_datadir_creates_missing_directory() {
        let root = unique_temp_test_path("test_create");
        let nested = root.join("test_nested").join("datadir");

        let resolved = resolve_datadir(&nested).expect("Missing directory creation failed.");

        assert_eq!(resolved, nested);
        assert!(nested.is_dir());

        let _ = fs::remove_dir_all(&root);
    }

    #[test]
    fn resolve_datadir_accepts_existing_directory() {
        let dir = unique_temp_test_path("test_existing");
        fs::create_dir_all(&dir).expect("Test directory creation failed.");

        let resolved = resolve_datadir(&dir).expect("Existing directory not resolved.");

        assert_eq!(resolved, dir);
        assert!(dir.is_dir());

        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn resolve_datadir_rejects_path_that_is_not_a_directory() {
        let file_path = unique_temp_test_path("test_file");
        fs::write(&file_path, b"not a directory").expect("Test file creation failed.");

        let error = resolve_datadir(&file_path).expect_err("a file must not be accepted");

        assert_eq!(error.kind(), ErrorKind::InvalidInput);
        assert!(file_path.is_file());

        let _ = fs::remove_file(&file_path);
    }

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
}
