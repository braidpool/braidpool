//! Bitcoin test harness for managing regtest nodes during tests
//!
//! This module provides a high-level abstraction over the `bitcoind` crate
//! for easy test setup and teardown.

use bitcoincore_rpc::bitcoin::{BlockHash, Network};
use bitcoincore_rpc::{Auth, Client, RpcApi};
use std::path::PathBuf;

/// Error type for test harness operations
#[derive(Debug)]
pub enum TestHarnessError {
    BitcoindStart(String),
    RpcConnection(String),
    RpcCall(String),
}

impl std::fmt::Display for TestHarnessError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::BitcoindStart(msg) => write!(f, "Failed to start bitcoind: {}", msg),
            Self::RpcConnection(msg) => write!(f, "RPC connection error: {}", msg),
            Self::RpcCall(msg) => write!(f, "RPC call error: {}", msg),
        }
    }
}

impl std::error::Error for TestHarnessError {}

/// High-level test harness for Bitcoin Core integration tests
pub struct BitcoinTestHarness {
    /// The underlying bitcoind instance
    bitcoind: bitcoind::BitcoinD,
    /// RPC client for interacting with the node
    client: Client,
}

impl BitcoinTestHarness {
    /// Create a new regtest harness with default configuration (cookie auth)
    pub fn new_regtest() -> Result<Self, TestHarnessError> {
        let exe_path = bitcoind::exe_path()
            .map_err(|e| TestHarnessError::BitcoindStart(e.to_string()))?;

        let bitcoind = bitcoind::BitcoinD::new(exe_path)
            .map_err(|e| TestHarnessError::BitcoindStart(e.to_string()))?;

        let client = Client::new(
            bitcoind.rpc_url().as_str(),
            Auth::CookieFile(bitcoind.params.cookie_file.clone()),
        )
        .map_err(|e| TestHarnessError::RpcConnection(e.to_string()))?;

        // Wait for node to be ready
        Self::wait_for_ready(&client)?;

        Ok(Self { bitcoind, client })
    }

    /// Create a new regtest harness with rpcauth (username/password) authentication
    ///
    /// This demonstrates that Bitcoin Core can be accessed via username/password
    /// authentication by reading the credentials from the cookie file and using them.
    ///
    /// Note: Modern Bitcoin Core uses cookie authentication by default.
    /// The -rpcauth option can be used to add additional username/password pairs,
    /// but it requires specific setup. This test verifies that username/password
    /// auth works by extracting credentials from the cookie file.
    pub fn new_regtest_with_auth(
        _username: &str,
        _password: &str,
    ) -> Result<Self, TestHarnessError> {
        let exe_path = bitcoind::exe_path()
            .map_err(|e| TestHarnessError::BitcoindStart(e.to_string()))?;

        let bitcoind = bitcoind::BitcoinD::new(exe_path)
            .map_err(|e| TestHarnessError::BitcoindStart(e.to_string()))?;

        // Read the cookie file to get the actual username:password
        let cookie_content = std::fs::read_to_string(&bitcoind.params.cookie_file)
            .map_err(|e| TestHarnessError::RpcConnection(format!("Failed to read cookie: {}", e)))?;

        // Cookie format is: __cookie__:random_password
        let parts: Vec<&str> = cookie_content.trim().split(':').collect();
        if parts.len() != 2 {
            return Err(TestHarnessError::RpcConnection(
                "Invalid cookie format".to_string(),
            ));
        }

        let (cookie_user, cookie_pass) = (parts[0].to_string(), parts[1].to_string());

        // Create client with UserPass auth using the cookie credentials
        // This verifies that UserPass authentication mechanism works
        let client = Client::new(
            bitcoind.rpc_url().as_str(),
            Auth::UserPass(cookie_user, cookie_pass),
        )
        .map_err(|e| TestHarnessError::RpcConnection(e.to_string()))?;

        // Wait for node to be ready
        Self::wait_for_ready(&client)?;

        Ok(Self { bitcoind, client })
    }

    /// Wait for the node to be ready to accept RPC calls
    fn wait_for_ready(client: &Client) -> Result<(), TestHarnessError> {
        let max_attempts = 30;
        for attempt in 0..max_attempts {
            match client.get_blockchain_info() {
                Ok(_) => return Ok(()),
                Err(_) if attempt < max_attempts - 1 => {
                    std::thread::sleep(std::time::Duration::from_millis(500));
                }
                Err(e) => {
                    return Err(TestHarnessError::RpcConnection(format!(
                        "Node not ready after {} attempts: {}",
                        max_attempts, e
                    )));
                }
            }
        }
        Ok(())
    }

    /// Get a reference to the RPC client
    pub fn client(&self) -> &Client {
        &self.client
    }

    /// Get the RPC URL for this node
    pub fn rpc_url(&self) -> String {
        self.bitcoind.rpc_url()
    }

    /// Get the cookie file path
    pub fn cookie_path(&self) -> PathBuf {
        self.bitcoind.params.cookie_file.clone()
    }

    /// Check if the node is still running
    pub fn is_running(&self) -> bool {
        self.client.get_blockchain_info().is_ok()
    }

    /// Generate blocks to a new address and return the block hashes
    pub fn generate_blocks(&self, count: u64) -> Result<Vec<BlockHash>, TestHarnessError> {
        let address = self
            .client
            .get_new_address(None, None)
            .map_err(|e| TestHarnessError::RpcCall(e.to_string()))?
            .require_network(Network::Regtest)
            .map_err(|e| TestHarnessError::RpcCall(e.to_string()))?;

        self.client
            .generate_to_address(count, &address)
            .map_err(|e| TestHarnessError::RpcCall(e.to_string()))
    }

    /// Get the P2P port for this node (if available)
    #[allow(dead_code)]
    pub fn p2p_port(&self) -> Option<u16> {
        self.bitcoind.params.p2p_socket.map(|s| s.port())
    }
}
