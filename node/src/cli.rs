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
    // wont-fix: None unreachable at runtime (default_value ensures Some) but kept for type consistency
    #[arg(long, default_value = "main")]
    pub network: Option<String>,

    /// Full path to bitcoind .cookie file for authentication.
    /// Auto-detected per OS and network if not specified:
    ///   Linux:  ~/.bitcoin/{network}/.cookie
    ///   macOS:  ~/Library/Application Support/Bitcoin/{network}/.cookie
    /// When bitcoind uses a custom -datadir (e.g., -datadir=/data/node1),
    /// the cookie file is at <datadir>/<network>/.cookie.
    /// Example: --rpccookie /data/node1/signet/.cookie
    /// Precedence: --rpccookie > config file cookie_path > auto-detect
    #[arg(long)]
    pub rpccookie: Option<String>,

    ///Rpc endpoints for the specific methods
    #[command(subcommand)]
    pub command: Option<RpcCommand>,

    /// Full path to the Bitcoin Core IPC Unix socket.
    /// This socket is created by bitcoind, not by braidpool.
    /// Bitcoind must be started with a matching -ipcbind flag:
    ///   bitcoin-node -ipcbind=unix:./braidpool/bitcoin-cpunet.sock
    /// The path passed to --ipc-socket must match exactly what was given to -ipcbind.
    /// Auto-detected defaults per network:
    ///   cpunet:   ./braidpool/bitcoin-cpunet.sock
    ///   mainnet:  ./braidpool/bitcoin-main.sock
    ///   testnet4: ./braidpool/bitcoin-testnet4.sock
    ///   signet:   ./braidpool/bitcoin-signet.sock
    ///   regtest:  ./braidpool/bitcoin-regtest.sock
    #[arg(long)]
    pub ipc_socket: Option<String>,
}
