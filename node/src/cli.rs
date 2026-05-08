use clap::Parser;
use std::net::SocketAddr;
use std::path::PathBuf;

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
    #[arg(long)]
    pub rpcpass: Option<String>,

    /// Which network to use. Valid options are mainnet, testnet4, signet, cpunet (preferred)
    #[arg(long, default_value = "main")]
    pub network: Option<String>,

    /// Use this cookie file for bitcoin RPC
    #[arg(long, default_value = "~/.bitcoin/.cookie")]
    pub rpccookie: Option<String>,

    /// TCP port for the local Stratum server
    #[arg(long, default_value_t = 3333)]
    pub stratum_port: u16,

    /// Bind address for the local node RPC server
    #[arg(long, default_value = "127.0.0.1:6682")]
    pub rpc_bind: SocketAddr,

    /// Path to Bitcoin Core IPC socket
    #[arg(long, default_value = "/tmp/bitcoin-cpunet.sock")]
    pub ipc_socket: String,
}

#[cfg(test)]
mod tests {
    use super::Cli;
    use clap::Parser;

    #[test]
    fn rpc_bind_parses_socket_address() {
        let cli = Cli::try_parse_from(["braid", "--rpc-bind", "127.0.0.1:1234"]).unwrap();

        assert_eq!(cli.rpc_bind.ip().to_string(), "127.0.0.1");
        assert_eq!(cli.rpc_bind.port(), 1234);
    }

    #[test]
    fn rpc_bind_rejects_address_without_port() {
        let result = Cli::try_parse_from(["braid", "--rpc-bind", "127.0.0.1"]);

        assert!(result.is_err());
    }
}
