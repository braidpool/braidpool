use bitcoin::Network;
use libp2p::core::multiaddr::{Multiaddr, Protocol};
use serde::{Deserialize, Serialize};
use std::fs;
use std::path::PathBuf;

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
    pub ipc_socket: Option<String>,
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
    pub fn load_from_config_file(
        path: &str,
    ) -> Result<BraidpoolConfig, Box<dyn std::error::Error>> {
        let contents = fs::read_to_string(path)?;
        let config: BraidpoolConfig = toml::from_str(&contents)?;

        Ok(config)
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

#[derive(Debug, Clone)]
pub struct CoinbaseConfig {
    pub network: Network,
    pub pool_payout_address: String,
    pub pool_identifier: String,
}

impl CoinbaseConfig {
    pub fn for_network(network: Network) -> Self {
        let pool_payout_address = match network {
            Network::Bitcoin => "bc1qpa77defz30uavu8lxef98q95rae6m7t8au9vp7".to_string(),
            Network::Testnet(_) => "tb1qpa77defz30uavu8lxef98q95rae6m7t8au9vp7".to_string(),
            Network::Signet => "tb1qpa77defz30uavu8lxef98q95rae6m7t8au9vp7".to_string(),
            Network::Regtest => "bcrt1qpa77defz30uavu8lxef98q95rae6m7t8au9vp7".to_string(),
            Network::CPUNet => "tc1qu3cdq9unyhdc3d2hw8mvpfgnnhvp6ucckkl6ft".to_string(),
            _ => "tb1qpa77defz30uavu8lxef98q95rae6m7t8au9vp7".to_string(),
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

    use super::{BitcoinConfig, BraidDirectoryConfig, BraidpoolConfig, NetworkConfig};
    #[test]
    pub fn config_building() {
        let cwd = std::env::current_dir()
            .unwrap()
            .join(Path::new("src/default_braidpool_config.toml"));

        let from_file = BraidpoolConfig::load_from_config_file(cwd.to_str().unwrap()).unwrap();

        let built = BraidpoolConfig {
            braidnetwork_config: NetworkConfig {
                listen_address: "/ip4/127.0.0.1/tcp/6885".to_string(),
                peer_nodes: vec![
                    "/ip4/127.0.0.1/tcp/1234".to_string(),
                    "/ip4/127.0.0.1/tcp/5678".to_string(),
                ],
            },
            bitcoin_config: BitcoinConfig {
                network: Network::CPUNet,
                username: "username".to_string(),
                password: "password".to_string(),
                port: "18443".to_string(),
                bitcoind_ip: "0.0.0.0".to_string(),
                cookie_path: "~/.bitcoin/regtest/.cookie".to_string(),
                ipc_socket: None,
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

pub fn expand_path(path: &str) -> PathBuf {
    PathBuf::from(
        shellexpand::full(path)
            .expect(&format!("Failed to expand path: {}", path))
            .into_owned(),
    )
}

pub fn expand_pathbuf(path: &PathBuf) -> PathBuf {
    expand_path(&path.to_string_lossy())
}

pub fn parse_network_arg(network_name: &str) -> Option<Network> {
    match network_name {
        "main" | "mainnet" => Some(Network::Bitcoin),
        "testnet" | "testnet4" => Some(Network::Testnet(bitcoin::TestnetVersion::V4)),
        "signet" => Some(Network::Signet),
        "regtest" => Some(Network::Regtest),
        "cpunet" => Some(Network::CPUNet),
        _ => None,
    }
}

pub fn socket_from_multiaddr(address: &str) -> Option<String> {
    let multiaddr: Multiaddr = address.parse().ok()?;
    let mut ip = None;
    let mut port = None;

    for protocol in multiaddr.into_iter() {
        match protocol {
            Protocol::Ip4(ipv4) => ip = Some(ipv4.to_string()),
            Protocol::Ip6(ipv6) => ip = Some(ipv6.to_string()),
            Protocol::Tcp(p) | Protocol::Udp(p) => port = Some(p),
            _ => {}
        }
    }

    match (ip, port) {
        (Some(ip), Some(port)) => Some(format!("{ip}:{port}")),
        _ => None,
    }
}
