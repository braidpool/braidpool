use bitcoin::block::HeaderExt;
use bitcoin::blockdata::block::ValidationError;
use bitcoin::hashes::{sha256d, HashEngine};
use bitcoin::{BlockHash, BlockHeader, Target};
use serde::{Deserialize, Serialize};
use std::fmt;

/// A network enum that extends `bitcoin::Network` with CPUNet support.
///
/// This avoids maintaining a full fork of rust-bitcoin just for the CPUNet variant.
/// Convert to `bitcoin::Network` via `.bitcoin_network()` when interacting with
/// upstream bitcoin library functions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BraidpoolNetwork {
    Bitcoin(bitcoin::Network),
    CPUNet,
}

impl BraidpoolNetwork {
    /// Returns the underlying `bitcoin::Network`, mapping CPUNet to Regtest
    /// for operations that require a standard network variant.
    pub fn bitcoin_network(&self) -> bitcoin::Network {
        match self {
            BraidpoolNetwork::Bitcoin(n) => *n,
            BraidpoolNetwork::CPUNet => bitcoin::Network::Regtest,
        }
    }

    pub fn is_cpunet(&self) -> bool {
        matches!(self, BraidpoolNetwork::CPUNet)
    }

    pub fn from_str_name(s: &str) -> Option<Self> {
        match s {
            "main" | "mainnet" | "bitcoin" => {
                Some(BraidpoolNetwork::Bitcoin(bitcoin::Network::Bitcoin))
            }
            "testnet" | "testnet4" => Some(BraidpoolNetwork::Bitcoin(bitcoin::Network::Testnet(
                bitcoin::TestnetVersion::V4,
            ))),
            "signet" => Some(BraidpoolNetwork::Bitcoin(bitcoin::Network::Signet)),
            "regtest" => Some(BraidpoolNetwork::Bitcoin(bitcoin::Network::Regtest)),
            "cpunet" => Some(BraidpoolNetwork::CPUNet),
            _ => None,
        }
    }
}

impl fmt::Display for BraidpoolNetwork {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BraidpoolNetwork::Bitcoin(n) => write!(f, "{}", n),
            BraidpoolNetwork::CPUNet => write!(f, "cpunet"),
        }
    }
}

impl Serialize for BraidpoolNetwork {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        match self {
            BraidpoolNetwork::Bitcoin(n) => n.serialize(serializer),
            BraidpoolNetwork::CPUNet => serializer.serialize_str("cpunet"),
        }
    }
}

impl<'de> Deserialize<'de> for BraidpoolNetwork {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = String::deserialize(deserializer)?;
        BraidpoolNetwork::from_str_name(&s)
            .ok_or_else(|| serde::de::Error::custom(format!("unknown network: {}", s)))
    }
}

impl From<bitcoin::Network> for BraidpoolNetwork {
    fn from(n: bitcoin::Network) -> Self {
        BraidpoolNetwork::Bitcoin(n)
    }
}

// --- CPUNet block hash ---

/// Computes the CPUNet block hash for a given header.
///
/// CPUNet appends `"cpunet\0"` to the standard 80-byte header serialization
/// before double-SHA256 hashing. This produces a different hash than the
/// standard Bitcoin `block_hash()`.
pub fn cpunet_block_hash(header: &BlockHeader) -> BlockHash {
    let mut engine = sha256d::Hash::engine();
    engine.input(&header.version.to_consensus().to_le_bytes());
    engine.input(header.prev_blockhash.as_byte_array());
    engine.input(header.merkle_root.as_byte_array());
    engine.input(&header.time.to_u32().to_le_bytes());
    engine.input(&header.bits.to_consensus().to_le_bytes());
    engine.input(&header.nonce.to_le_bytes());
    engine.input(b"cpunet\0");

    BlockHash::from_byte_array(sha256d::Hash::from_engine(engine).to_byte_array())
}

/// Returns the appropriate block hash for the given network.
/// Uses cpunet-modified hash for CPUNet, standard hash for all others.
pub fn block_hash_for_network(header: &BlockHeader, network: &BraidpoolNetwork) -> BlockHash {
    if network.is_cpunet() {
        cpunet_block_hash(header)
    } else {
        header.block_hash()
    }
}

/// Validates proof-of-work for a CPUNet block header.
///
/// This mirrors `HeaderExt::validate_pow` but uses the CPUNet-specific block hash
/// (with the `"cpunet\0"` suffix in the preimage).
pub fn cpunet_validate_pow(
    header: &BlockHeader,
    required_target: Target,
) -> Result<BlockHash, ValidationError> {
    let target: Target = header.bits.into();
    if target != required_target {
        return Err(ValidationError::BadTarget);
    }
    let block_hash = cpunet_block_hash(header);
    if target.is_met_by(block_hash) {
        Ok(block_hash)
    } else {
        Err(ValidationError::BadProofOfWork)
    }
}

/// Validates proof-of-work using the appropriate hash function for the network.
pub fn validate_pow_for_network(
    header: &BlockHeader,
    required_target: Target,
    network: &BraidpoolNetwork,
) -> Result<BlockHash, ValidationError> {
    if network.is_cpunet() {
        cpunet_validate_pow(header, required_target)
    } else {
        header.validate_pow(required_target)
    }
}

// --- CPUNet network constants ---

/// P2P magic bytes for CPUNet: ASCII "cpun"
pub const CPUNET_MAGIC: [u8; 4] = [0x63, 0x70, 0x75, 0x6E];

/// ChainHash for CPUNet (genesis block hash, reversed byte order).
pub const CPUNET_CHAIN_HASH: [u8; 32] = [
    155, 244, 9, 169, 207, 188, 132, 171, 5, 153, 89, 228, 109, 99, 3, 243, 57, 98, 248, 5, 188,
    141, 147, 51, 119, 165, 255, 187, 0, 0, 0, 0,
];

/// CPUNet genesis block timestamp.
pub const CPUNET_GENESIS_TIME: u32 = 1723652721;

/// CPUNet genesis block nonce.
pub const CPUNET_GENESIS_NONCE: u32 = 961348305;

/// CPUNet genesis block difficulty target (same as mainnet initial: 0x1d00ffff).
pub const CPUNET_GENESIS_BITS: u32 = 0x1d00ffff;

/// Default pool payout address for CPUNet.
///
/// Uses `bcrt1` (regtest) encoding since the standard bitcoin crate cannot parse
/// the cpunet-specific `tc1` bech32 HRP. CPUNet maps to regtest for address handling.
/// Operators should configure their own payout address.
pub const CPUNET_DEFAULT_PAYOUT_ADDRESS: &str = "bcrt1qpa77defz30uavu8lxef98q95rae6m7t8au9vp7";

/// Default IPC socket path for CPUNet.
pub const CPUNET_DEFAULT_IPC_SOCKET: &str = "/tmp/bitcoin-cpunet.sock";

// --- CPUNet address helpers ---

/// Returns the default pool payout address for the given network.
pub fn default_payout_address(network: &BraidpoolNetwork) -> String {
    match network {
        BraidpoolNetwork::CPUNet => CPUNET_DEFAULT_PAYOUT_ADDRESS.to_string(),
        BraidpoolNetwork::Bitcoin(n) => match n {
            bitcoin::Network::Bitcoin => "bc1qpa77defz30uavu8lxef98q95rae6m7t8au9vp7".to_string(),
            bitcoin::Network::Testnet(_) | bitcoin::Network::Signet => {
                "tb1qpa77defz30uavu8lxef98q95rae6m7t8au9vp7".to_string()
            }
            bitcoin::Network::Regtest => "bcrt1qpa77defz30uavu8lxef98q95rae6m7t8au9vp7".to_string(),
            _ => "tb1qpa77defz30uavu8lxef98q95rae6m7t8au9vp7".to_string(),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use bitcoin::{BlockTime, BlockVersion, CompactTarget, TxMerkleNode};

    fn test_header() -> BlockHeader {
        let zero_hash = BlockHash::from_byte_array([0u8; 32]);
        let zero_merkle = TxMerkleNode::from_byte_array([0u8; 32]);
        BlockHeader {
            version: BlockVersion::TWO,
            prev_blockhash: zero_hash,
            merkle_root: zero_merkle,
            time: BlockTime::from_u32(1653195600),
            bits: CompactTarget::from_consensus(0x1d00ffff),
            nonce: 42,
        }
    }

    #[test]
    fn cpunet_hash_differs_from_standard() {
        let header = test_header();
        let standard = header.block_hash();
        let cpunet = cpunet_block_hash(&header);
        assert_ne!(
            standard, cpunet,
            "CPUNet hash must differ from standard hash"
        );
    }

    #[test]
    fn block_hash_for_network_dispatches_correctly() {
        let header = test_header();
        let btc = BraidpoolNetwork::Bitcoin(bitcoin::Network::Bitcoin);
        let cpu = BraidpoolNetwork::CPUNet;

        assert_eq!(block_hash_for_network(&header, &btc), header.block_hash());
        assert_eq!(
            block_hash_for_network(&header, &cpu),
            cpunet_block_hash(&header)
        );
    }

    #[test]
    fn braidpool_network_serde_roundtrip() {
        let networks = vec![
            (BraidpoolNetwork::CPUNet, "\"cpunet\""),
            (
                BraidpoolNetwork::Bitcoin(bitcoin::Network::Bitcoin),
                "\"bitcoin\"",
            ),
        ];
        for (net, expected_json) in &networks {
            let json = serde_json::to_string(net).unwrap();
            assert_eq!(&json, expected_json);
            let back: BraidpoolNetwork = serde_json::from_str(&json).unwrap();
            assert_eq!(&back, net);
        }
    }

    #[test]
    fn braidpool_network_from_str() {
        assert_eq!(
            BraidpoolNetwork::from_str_name("cpunet"),
            Some(BraidpoolNetwork::CPUNet)
        );
        assert_eq!(
            BraidpoolNetwork::from_str_name("main"),
            Some(BraidpoolNetwork::Bitcoin(bitcoin::Network::Bitcoin))
        );
        assert_eq!(BraidpoolNetwork::from_str_name("unknown"), None);
    }

    #[test]
    fn braidpool_network_display() {
        assert_eq!(BraidpoolNetwork::CPUNet.to_string(), "cpunet");
        assert_eq!(
            BraidpoolNetwork::Bitcoin(bitcoin::Network::Bitcoin).to_string(),
            "bitcoin"
        );
    }
}
