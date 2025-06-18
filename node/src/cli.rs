use clap::Parser;
use std::path::PathBuf;

#[derive(Parser, Debug)]
pub struct Cli {
    /// Braid data directory
    #[arg(long, default_value = "~/.braidpool/")]
    pub datadir: PathBuf,

    /// Bind to a given address and always listen on it
    #[arg(long, default_value = "0.0.0.0:25188")]
    pub bind: String,

    /// Add a node to connect to and attempt to keep the connection open. This option can be
    /// specified multiple times
    #[arg(long)]
    pub addnode: Option<Vec<String>>,

    /// Connect to this bitcoin node
    #[arg(long, default_value = "0.0.0.0")]
    pub bitcoin: String,

    /// Use this port for bitcoin RPC
    #[arg(long, default_value = "8332")]
    pub rpcport: u16,

    /// Use this username for bitcoin RPC
    #[arg(long)]
    pub rpcuser: Option<String>,

    /// Use this password for bitcoin RPC
    #[arg(long, default_value = "")]
    pub rpcpass: Option<String>,

    /// Which network to use. Valid options are mainnet, testnet4, signet, cpunet (preferred)
    #[arg(long, default_value = "main")]
    pub network: Option<String>,

    /// Use this cookie file for bitcoin RPC
    #[arg(long, default_value = "~/.bitcoin/.cookie")]
    pub rpccookie: Option<String>,

    /// Use this port for bitcoin ZMQ
    #[arg(long, default_value = "28332")]
    pub zmqhashblockport: u16,

    #[arg(long, action = clap::ArgAction::SetTrue)]
    pub ipc: bool,
    
    /// Path to Bitcoin Core IPC socket
    #[arg(long, default_value = "/tmp/bitcoin-ipc.sock")]
    pub socket: String,
}
