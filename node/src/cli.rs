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

    /// Connect to this bitcoin RPC node
    #[arg(long, default_value = "0.0.0.0:38332")]
    pub rpc_url: String,

    /// Use this username for bitcoin RPC
    #[arg(long, default_value = "braidpooldev")]
    pub rpc_user: String,

    /// Use this password for bitcoin RPC
    #[arg(long, default_value = "braidpooldev")]
    pub rpc_pass: String,

    /// Interval for polling bitcoin RPC for new block templates (seconds)
    #[arg(long, default_value = "10")]
    pub poll_interval: u64,
}
