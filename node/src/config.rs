use bitcoin::Network;
use libp2p::core::multiaddr::{Multiaddr, Protocol};
use serde::{Deserialize, Serialize};
use std::error::Error;
use std::fs;
use std::path::PathBuf;
use tracing::{error, info};

// Default network configuration constants
/// Default bind address for the braidpool node
pub const DEFAULT_BIND_ADDRESS: &str = "0.0.0.0:6680";
/// Default port for braidpool P2P communication
pub const DEFAULT_P2P_PORT: u16 = 6680;
/// Default Bitcoin RPC port (regtest)
pub const DEFAULT_BITCOIN_RPC_PORT: u16 = 18443;
/// Default braidpool RPC server address
pub const DEFAULT_RPC_SERVER_ADDR: &str = "127.0.0.1:6682";
/// Default data directory path
pub const DEFAULT_DATA_DIR: &str = "~/.braidpool";
/// Default Bitcoin cookie path
pub const DEFAULT_COOKIE_PATH: &str = "~/.bitcoin/regtest/.cookie";
/// Default pool identifier
pub const DEFAULT_POOL_IDENTIFIER: &str = "Braidpool";
#[derive(Deserialize, Serialize, Clone)]
pub struct NetworkConfig {
    //Address to which the current braidpool node will bind to
    pub listen_address: String,
    //peer nodes to be added subscribed to the same topic
    pub peer_nodes: Vec<String>,
}

impl Default for NetworkConfig {
    fn default() -> Self {
        NetworkConfig {
            listen_address: format!("/ip4/0.0.0.0/udp/{}/quic-v1", DEFAULT_P2P_PORT),
            peer_nodes: Vec::new(),
        }
    }
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

impl Default for BitcoinConfig {
    fn default() -> Self {
        BitcoinConfig {
            network: Network::Regtest,
            username: String::new(),
            password: String::new(),
            port: DEFAULT_BITCOIN_RPC_PORT.to_string(),
            bitcoind_ip: "127.0.0.1".to_string(),
            cookie_path: DEFAULT_COOKIE_PATH.to_string(),
            ipc_socket: None,
        }
    }
}

#[derive(Serialize, Deserialize, Clone)]
pub struct BraidDirectoryConfig {
    pub path: String,
}

impl Default for BraidDirectoryConfig {
    fn default() -> Self {
        BraidDirectoryConfig {
            path: DEFAULT_DATA_DIR.to_string(),
        }
    }
}

#[derive(Serialize, Deserialize, Clone)]
pub struct MinerConfig {
    pub miner_pubkey: String,
}

impl Default for MinerConfig {
    fn default() -> Self {
        MinerConfig {
            miner_pubkey: String::new(),
        }
    }
}

#[derive(Serialize, Deserialize, Clone)]
pub struct BraidpoolConfig {
    pub braidnetwork_config: NetworkConfig,
    pub bitcoin_config: BitcoinConfig,
    pub braid_directory: BraidDirectoryConfig,
    pub miner_config: MinerConfig,
    pub braid_rpc_config: BraidRpcConfig,
}

impl Default for BraidpoolConfig {
    fn default() -> Self {
        BraidpoolConfig {
            braidnetwork_config: NetworkConfig::default(),
            bitcoin_config: BitcoinConfig::default(),
            braid_directory: BraidDirectoryConfig::default(),
            miner_config: MinerConfig::default(),
            braid_rpc_config: BraidRpcConfig::default(),
        }
    }
}

#[derive(Serialize, Deserialize, Clone)]
//Rpc server configuration
pub struct BraidRpcConfig {
    pub rpc_server_addr: String,
}
impl Default for BraidRpcConfig {
    fn default() -> Self {
        BraidRpcConfig {
            rpc_server_addr: DEFAULT_RPC_SERVER_ADDR.to_string(),
        }
    }
}

#[derive(Debug, Clone)]
pub struct RuntimeConfig {
    pub datadir: PathBuf,
    pub bind_addr: String,
    pub peer_nodes: Vec<String>,
    pub network: Network,
    pub ipc_socket: String,
    pub rpc_server_addr: String,
}

pub fn load_runtime_config(args: &crate::cli::Cli) -> Result<RuntimeConfig, Box<dyn Error>> {
    let config_path = expand_pathbuf(&args.config);
    if !config_path.exists() {
        error!(path = %config_path.display(), "Config file not found");
        return Err(std::io::Error::new(
            std::io::ErrorKind::NotFound,
            format!("Config file not found at {}", config_path.display()),
        )
        .into());
    }

    info!(path = %config_path.display(), "Loading braidpool config");
    let braidpool_config = match BraidpoolConfig::load_from_config_file(
        config_path
            .to_str()
            .expect("Failed to convert config path to string"),
    ) {
        Ok(c) => c,
        Err(e) => {
            error!(error = %e, path = %config_path.display(), "Invalid configuration file");
            return Err(e);
        }
    };

    let datadir = match args.datadir.as_ref() {
        Some(path) => expand_pathbuf(path),
        None => expand_path(&braidpool_config.braid_directory.path),
    };

    let bind_addr = args
        .bind
        .clone()
        .or_else(|| socket_from_multiaddr(&braidpool_config.braidnetwork_config.listen_address))
        .unwrap_or_else(|| DEFAULT_BIND_ADDRESS.to_string());

    let mut peer_nodes = braidpool_config.braidnetwork_config.peer_nodes.clone();
    if let Some(nodes) = args.addnode.clone() {
        peer_nodes.extend(nodes);
    }

    let network = match args.network.as_deref() {
        Some(network_name) => match parse_network_arg(network_name) {
            Some(parsed) => parsed,
            None => {
                error!(
                    network = %network_name,
                    valid_networks = "main, testnet, testnet4, signet, regtest, cpunet",
                    "Invalid network specified, falling back to config value"
                );
                braidpool_config.bitcoin_config.network
            }
        },
        None => braidpool_config.bitcoin_config.network,
    };

    let ipc_socket = braidpool_config
        .bitcoin_config
        .ipc_socket
        .clone()
        .unwrap_or(args.ipc_socket.clone());

    let rpc_server_addr = braidpool_config.braid_rpc_config.rpc_server_addr.clone();

    let bitcoin_node = args
        .bitcoin
        .clone()
        .unwrap_or_else(|| braidpool_config.bitcoin_config.bitcoind_ip.clone());

    let rpc_port = args
        .rpcport
        .or_else(|| {
            braidpool_config
                .bitcoin_config
                .port
                .parse::<u16>()
                .map_err(|e| {
                    error!("Invalid port number in config: {}", e);
                    e
                })
                .ok()
        })
        .unwrap_or(DEFAULT_BITCOIN_RPC_PORT);

    let rpc_user = args
        .rpcuser
        .clone()
        .unwrap_or_else(|| braidpool_config.bitcoin_config.username.clone());

    let _rpc_pass = args
        .rpcpass
        .clone()
        .unwrap_or_else(|| braidpool_config.bitcoin_config.password.clone());

    let _rpc_cookie = args
        .rpccookie
        .clone()
        .map(|p| expand_path(&p))
        .or_else(|| Some(expand_path(&braidpool_config.bitcoin_config.cookie_path)));

    info!(
        bitcoin_node = %bitcoin_node,
        rpc_port = %rpc_port,
        rpc_user = %rpc_user,
        "Bitcoin RPC configuration loaded"
    );

    match fs::metadata(&datadir) {
        Ok(m) => {
            if !m.is_dir() {
                error!(
                    datadir = %datadir.display(),
                    "Data directory exists but is not a directory"
                );
            }
            info!(datadir = %datadir.display(), "Using existing data directory");
        }
        Err(_) => {
            info!(datadir = %datadir.display(), "Creating data directory");
            fs::create_dir_all(&datadir)?;
        }
    }

    Ok(RuntimeConfig {
        datadir,
        bind_addr,
        peer_nodes,
        network,
        ipc_socket,
        rpc_server_addr,
    })
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
