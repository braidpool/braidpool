use std::process;
use log;
use tokio::sync::broadcast;

/// Reason for shutting down the node
#[derive(Debug, Clone)]
pub enum ShutdownReason {
    BitcoinNodeError(String),
    UserInitiated,
    ConnectionError(String),
}

/// Handles graceful shutdown of the node
#[derive(Clone)]
pub struct ShutdownHandler {
    shutdown_tx: broadcast::Sender<ShutdownReason>,
}

impl ShutdownHandler {
    /// Creates a new shutdown handler
    pub fn new() -> (Self, broadcast::Receiver<ShutdownReason>) {
        let (shutdown_tx, shutdown_rx) = broadcast::channel(1);
        (ShutdownHandler { shutdown_tx }, shutdown_rx)
    }

    /// Initiates shutdown due to Bitcoin node error
    pub fn shutdown_bitcoin_error(&self, error: String) {
        log::error!("Bitcoin node error: {}", error);
        if let Err(e) = self.shutdown_tx.send(ShutdownReason::BitcoinNodeError(error)) {
            log::error!("Failed to send shutdown signal: {}", e);
        }
        process::exit(1);
    }

    /// Initiates shutdown due to connection error
    pub fn shutdown_connection_error(&self, error: String) {
        log::error!("Connection error: {}", error);
        if let Err(e) = self.shutdown_tx.send(ShutdownReason::ConnectionError(error)) {
            log::error!("Failed to send shutdown signal: {}", e);
        }
        process::exit(1);
    }

    /// Initiates user-requested shutdown
    pub fn shutdown_user_initiated(&self) {
        log::info!("User initiated shutdown");
        if let Err(e) = self.shutdown_tx.send(ShutdownReason::UserInitiated) {
            log::error!("Failed to send shutdown signal: {}", e);
        }
        process::exit(0);
    }
} 