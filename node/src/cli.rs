use clap::Parser;
use std::path::PathBuf;

#[derive(Parser, Debug, Clone)]
#[command(name = "braid", about = "Braidpool Node CLI")]
pub struct Cli {
    /// Path to braidpool config file (TOML)
    #[arg(long, default_value = concat!(env!("CARGO_MANIFEST_DIR"), "/src/default_braidpool_config.toml"))]
    pub config: PathBuf,

    /// Braid data directory
    #[arg(long)]
    pub datadir: Option<PathBuf>,

    /// Bind to a given address and always listen on it
    #[arg(long)]
    pub bind: Option<String>,

    /// Add a node to connect to and attempt to keep the connection open. This option can be
    /// specified multiple times
    #[arg(long)]
    pub addnode: Option<Vec<String>>,

    /// Connect to this bitcoin node
    #[arg(long)]
    pub bitcoin: Option<String>,

    /// Use this port for bitcoin RPC
    #[arg(long)]
    pub rpcport: Option<u16>,

    /// Use this username for bitcoin RPC
    #[arg(long)]
    pub rpcuser: Option<String>,

    /// Use this password for bitcoin RPC
    #[arg(long)]
    pub rpcpass: Option<String>,

    /// Which network to use. Valid options are mainnet, testnet4, signet, cpunet (preferred)
    #[arg(long)]
    pub network: Option<String>,

    /// Use this cookie file for bitcoin RPC
    #[arg(long)]
    pub rpccookie: Option<String>,

    /// Path to Bitcoin Core IPC socket
    #[arg(long, default_value = "/tmp/bitcoin-cpunet.sock")]
    pub ipc_socket: String,
}
