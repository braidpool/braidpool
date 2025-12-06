//! Error types for the braidpool node
//!
//! This module defines typed error enums for different subsystems of the node.

use thiserror::Error;

/// Errors related to node initialization and operation
#[derive(Error, Debug)]
pub enum NodeError {
    #[error("Invalid path encoding: {0}")]
    InvalidPath(String),

    #[error("Shell expansion failed: {0}")]
    ShellExpansion(String),

    #[error("Tracing setup failed: {0}")]
    TracingSetup(String),

    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
}

/// Errors related to protocol message handling
#[derive(Error, Debug)]
pub enum ProtocolError {
    #[error("Serialization failed: {0}")]
    Serialization(String),

    #[error("Message creation failed: no message available")]
    MessageCreation,
}

/// Errors related to RPC operations
#[derive(Error, Debug)]
pub enum RpcError {
    #[error("RPC authentication not configured: missing {0}")]
    MissingAuth(String),

    #[error("RPC call failed: {0}")]
    RpcCall(#[from] bitcoincore_rpc::Error),
}

/// Errors related to braid operations
#[derive(Error, Debug)]
pub enum BraidError {
    #[error("Bead work not found for bead: {0}")]
    BeadWorkNotFound(String),

    #[error("Empty bead collection - cannot find maximum")]
    EmptyBeadCollection,
}

