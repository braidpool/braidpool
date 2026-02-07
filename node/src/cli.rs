use clap::Parser;
use std::path::PathBuf;

use crate::rpc_server::RpcCommand;

#[derive(Parser, Debug, Clone)]
#[command(name = "braid", about = "Braidpool Node CLI")]
pub struct Cli {
    /// Braid data directory
    #[arg(long, default_value = "~/.braidpool/")]
    pub datadir: PathBuf,

    /// Bind to a given address and always listen on it
    #[arg(long, default_value = "0.0.0.0:6680")]
    pub bind: String,

    /// Add a node to connect to and attempt to keep the connection open. This option can be
    /// specified multiple times
    #[arg(long)]
    pub addnode: Option<Vec<String>>,

    /// Which network to use. Valid options are mainnet, testnet4, signet, cpunet (preferred)
    #[arg(long, default_value = "main")]
    pub network: Option<String>,

    /// Full path to bitcoind .cookie file for authentication.
    /// When bitcoind uses a custom -datadir (e.g., -datadir=/data/node1),
    /// the cookie file is at <datadir>/<network>/.cookie.
    /// Example: --rpccookie /data/node1/signet/.cookie
    /// Precedence: --rpccookie > config file cookie_path > auto-detect from ~/.bitcoin/
    #[arg(long)]
    pub rpccookie: Option<String>,

    ///Rpc endpoints for the specific methods
    #[command(subcommand)]
    pub command: Option<RpcCommand>,

    /// Path to Bitcoin Core IPC socket. Auto-detected per network if not specified.
    #[arg(long)]
    pub ipc_socket: Option<String>,
}
