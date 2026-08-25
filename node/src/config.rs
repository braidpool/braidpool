use crate::error::UnsupportedNetworkError;
use bitcoin::{block::Header, BlockHash, Network};
use braidpool_common::cpunet::{Cpunet, CPUNET_NAME};
use core::fmt;
use core::panic;
use serde::{Deserialize, Serialize};
use std::fs;
use std::str::FromStr;
#[derive(Deserialize, Serialize, Clone)]
pub struct NetworkConfig {
    //Address to which the current braidpool node will bind to
    pub listen_address: String,
    //peer nodes to be added subscribed to the same topic
    pub peer_nodes: Vec<String>,
}
#[derive(Serialize, Deserialize, Clone)]
pub struct BitcoinConfig {
    pub network: bitcoin::Network,
    pub username: String,
    pub password: String,
    pub port: String,
    pub bitcoind_ip: String,
    pub cookie_path: String,
}
#[derive(Serialize, Deserialize, Clone)]
pub struct BraidDirectoryConfig {
    pub path: String,
}
#[derive(Serialize, Deserialize, Clone)]
pub struct MinerConfig {
    pub miner_pubkey: String,
}
#[derive(Serialize, Deserialize, Clone)]
pub struct BraidpoolConfig {
    pub braidnetwork_config: NetworkConfig,
    pub bitcoin_config: BitcoinConfig,
    pub braid_directory: BraidDirectoryConfig,
    pub miner_config: MinerConfig,
    pub braid_rpc_config: BraidRpcConfig,
}
#[derive(Serialize, Deserialize, Clone)]
//Rpc server configuration
pub struct BraidRpcConfig {
    pub rpc_server_addr: String,
}
impl Default for BraidRpcConfig {
    fn default() -> Self {
        BraidRpcConfig {
            rpc_server_addr: String::from("127.0.0.1:6682"),
        }
    }
}
#[allow(dead_code)]
impl BraidpoolConfig {
    pub fn load_from_config_file(path: &str) -> BraidpoolConfig {
        let contents = match fs::read_to_string(path) {
            Ok(c) => c,
            Err(error) => {
                panic!("An error occurred while reading the file {}", error);
            }
        };
        let config: BraidpoolConfig = toml::from_str(&contents).unwrap();

        config
    }
    pub fn with_listen_address(mut self, listen_address: String) -> Self {
        self.braidnetwork_config.listen_address = listen_address;
        return self;
    }
    pub fn with_peer_nodes(mut self, peers: Vec<String>) -> Self {
        self.braidnetwork_config.peer_nodes = peers;
        self
    }

    pub fn with_network(mut self, network: bitcoin::Network) -> Self {
        self.bitcoin_config.network = network;
        self
    }

    pub fn with_username(mut self, username: String) -> Self {
        self.bitcoin_config.username = username;
        self
    }

    pub fn with_password(mut self, password: String) -> Self {
        self.bitcoin_config.password = password;
        self
    }

    pub fn with_port(mut self, port: String) -> Self {
        self.bitcoin_config.port = port;
        self
    }

    pub fn with_bitcoind_ip(mut self, ip: String) -> Self {
        self.bitcoin_config.bitcoind_ip = ip;
        self
    }

    pub fn with_cookie_path(mut self, path: String) -> Self {
        self.bitcoin_config.cookie_path = path;
        self
    }

    pub fn with_braid_store_path(mut self, path: String) -> Self {
        self.braid_directory.path = path;
        self
    }
}
// Supporting network types and their aliases
pub const MAINNET_NAME: &str = "mainnet";
pub const TESTNET_NAME: &str = "testnet";
pub const TESTNET4_NAME: &str = "testnet4";
pub const SIGNET_NAME: &str = "signet";
pub const REGTEST_NAME: &str = "regtest";

/// The set of network names a braidpool node accepts.
pub const SUPPORTED_NETWORKS: [&str; 6] = [
    MAINNET_NAME,
    TESTNET_NAME,
    TESTNET4_NAME,
    SIGNET_NAME,
    REGTEST_NAME,
    CPUNET_NAME,
];

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum PoolNetwork {
    /// The cpunet test network, whose block hash is computed by [`Cpunet::block_hash`].
    Cpunet,
    /// A network other than native rust-bitcoin
    Bitcoin(Network),
}

impl PoolNetwork {
    /// Resolves a network name to a [`PoolNetwork`].
    pub fn from_name(name: &str) -> Option<Self> {
        match name {
            CPUNET_NAME => Some(Self::Cpunet),
            MAINNET_NAME => Some(Self::Bitcoin(Network::Bitcoin)),
            TESTNET_NAME => Some(Self::Bitcoin(Network::Testnet)),
            TESTNET4_NAME => Some(Self::Bitcoin(Network::Testnet4)),
            SIGNET_NAME => Some(Self::Bitcoin(Network::Signet)),
            REGTEST_NAME => Some(Self::Bitcoin(Network::Regtest)),
            _ => None,
        }
    }

    /// Returns the network name, round-tripping with [`PoolNetwork::from_name`].
    pub fn name(&self) -> &'static str {
        match self {
            Self::Cpunet => CPUNET_NAME,
            Self::Bitcoin(Network::Bitcoin) => MAINNET_NAME,
            Self::Bitcoin(Network::Testnet) => TESTNET_NAME,
            Self::Bitcoin(Network::Testnet4) => TESTNET4_NAME,
            Self::Bitcoin(Network::Signet) => SIGNET_NAME,
            Self::Bitcoin(Network::Regtest) => REGTEST_NAME,
        }
    }

    /// Returns whether this is the cpunet network.
    pub const fn is_cpunet(&self) -> bool {
        matches!(self, Self::Cpunet)
    }

    /// Computes the block hash of `header` under this network's rules.
    pub fn block_hash(&self, header: &Header) -> BlockHash {
        match self {
            Self::Cpunet => Cpunet::block_hash(header),
            Self::Bitcoin(_) => header.block_hash(),
        }
    }
}

impl fmt::Display for PoolNetwork {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.name())
    }
}

impl FromStr for PoolNetwork {
    type Err = UnsupportedNetworkError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        parse_network_name(s)
    }
}

/// Resolves a network name to its [`PoolNetwork`].
///
/// # Arguments
/// * `network_name` - One of [`SUPPORTED_NETWORKS`], matched exactly
///
/// # Returns
/// The [`PoolNetwork`] the name denotes. Cpunet has no `bitcoin::Network` variant and is carried
/// as [`PoolNetwork::Cpunet`].
///
/// # Errors
/// [`UnsupportedNetworkError`] if `network_name` is not in [`SUPPORTED_NETWORKS`].
pub fn parse_network_name(network_name: &str) -> Result<PoolNetwork, UnsupportedNetworkError> {
    PoolNetwork::from_name(network_name).ok_or_else(|| UnsupportedNetworkError {
        network_name: network_name.to_string(),
    })
}

#[derive(Debug, Clone)]
pub struct CoinbaseConfig {
    pub network: PoolNetwork,
    pub pool_payout_address: String,
    pub pool_identifier: String,
}

impl CoinbaseConfig {
    /// Creates CoinbaseConfig for an already-resolved [`PoolNetwork`].
    ///
    /// The payout address is chosen from the network, so it can never be
    /// silently coerced onto a default chain, which would produce shares and
    /// payout addresses for the wrong chain.
    pub fn from_network(network: PoolNetwork) -> Self {
        let pool_payout_address = match network {
            PoolNetwork::Cpunet => "tc1qu3cdq9unyhdc3d2hw8mvpfgnnhvp6ucckkl6ft".to_string(),
            PoolNetwork::Bitcoin(Network::Bitcoin) => {
                "bc1qpa77defz30uavu8lxef98q95rae6m7t8au9vp7".to_string()
            }
            PoolNetwork::Bitcoin(Network::Regtest) => {
                "bcrt1qpa77defz30uavu8lxef98q95rae6m7t8au9vp7".to_string()
            }
            PoolNetwork::Bitcoin(_) => "tb1qpa77defz30uavu8lxef98q95rae6m7t8au9vp7".to_string(),
        };

        Self {
            network,
            pool_payout_address,
            pool_identifier: "Braidpool".to_string(),
        }
    }
}

#[cfg(test)]
mod test {
    use std::path::Path;

    use bitcoin::Network;

    use crate::config::{BraidRpcConfig, MinerConfig};

    use super::{
        BitcoinConfig, BraidDirectoryConfig, BraidpoolConfig, NetworkConfig, PoolNetwork,
        SUPPORTED_NETWORKS,
    };

    #[test]
    fn every_supported_name_round_trips() {
        for name in SUPPORTED_NETWORKS {
            let network = PoolNetwork::from_name(name)
                .unwrap_or_else(|| panic!("'{}' should be a supported network", name));
            assert_eq!(network.name(), name);
            assert_eq!(network.to_string(), name);
        }
    }
    #[test]
    pub fn config_building() {
        let cwd = std::env::current_dir()
            .unwrap()
            .join(Path::new("src/default_braidpool_config.toml"));

        let from_file = BraidpoolConfig::load_from_config_file(cwd.to_str().unwrap());

        let built = BraidpoolConfig {
            braidnetwork_config: NetworkConfig {
                listen_address: "/ip4/127.0.0.1/tcp/6885".to_string(),
                peer_nodes: vec![
                    "/ip4/127.0.0.1/tcp/1234".to_string(),
                    "/ip4/127.0.0.1/tcp/5678".to_string(),
                ],
            },
            bitcoin_config: BitcoinConfig {
                network: Network::Regtest,
                username: "username".to_string(),
                password: "password".to_string(),
                port: "18443".to_string(),
                bitcoind_ip: "0.0.0.0".to_string(),
                cookie_path: "~/.bitcoin/regtest/.cookie".to_string(),
            },
            braid_directory: BraidDirectoryConfig {
                path: "~/.braidpool".to_string(),
            },
            miner_config: MinerConfig {
                miner_pubkey: "".to_string(),
            },
            braid_rpc_config: BraidRpcConfig::default(),
        };
        assert_eq!(
            from_file.braidnetwork_config.listen_address,
            built.braidnetwork_config.listen_address
        );
        assert_eq!(
            from_file.braidnetwork_config.peer_nodes,
            built.braidnetwork_config.peer_nodes
        );
        assert_eq!(
            from_file.bitcoin_config.network,
            built.bitcoin_config.network
        );
        assert_eq!(
            from_file.bitcoin_config.username,
            built.bitcoin_config.username
        );
        assert_eq!(
            from_file.bitcoin_config.password,
            built.bitcoin_config.password
        );
        assert_eq!(from_file.bitcoin_config.port, built.bitcoin_config.port);
        assert_eq!(
            from_file.bitcoin_config.bitcoind_ip,
            built.bitcoin_config.bitcoind_ip
        );
        assert_eq!(
            from_file.bitcoin_config.cookie_path,
            built.bitcoin_config.cookie_path
        );
        assert_eq!(from_file.braid_directory.path, built.braid_directory.path);
        assert_eq!(
            from_file.braid_rpc_config.rpc_server_addr,
            built.braid_rpc_config.rpc_server_addr
        );
    }
}
