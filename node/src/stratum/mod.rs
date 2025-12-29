//! Stratum V1 Protocol Implementation for Braidpool
//!
//! This module implements the Stratum V1 mining protocol for Braidpool,
//! providing compatibility with standard Stratum V1 miners.
//!
//! # Module Structure
//!
//! - `core` - Core Stratum implementation (original braidpool code)
//! - `sv1_compat` - Compatibility layer with official `sv1_api` types
//! - `sv1_server_impl` - Implementation of `sv1_api::IsServer` trait
//!
//! # Migration Status (Issue #313)
//!
//! This module is currently being migrated to use the official `sv1_api` crate
//! from the Stratum Reference Implementation (SRI) project.
//!
//! **Current Status:**
//! - ✅ `sv1_api` dependency added
//! - ✅ Compatibility layer created
//! - ✅ `IsServer` trait skeleton implemented
//! - ✅ Type conversion implementation (From/Into traits)
//! - ✅ `handle_configure` method implemented
//! - ✅ `handle_subscribe` method implemented
//! - ✅ `handle_authorize` and authorization methods implemented
//! - ✅ Extranonce management methods implemented
//! - ✅ `handle_submit` method implemented (simplified stub)
//! - ✅ Message parsing updated to use `sv1_api::json_rpc::Message` (with legacy fallback)
//! - ⏳ Full message routing via `IsServer` trait (currently falls back to legacy routing)
//! - ⏳ Remaining `IsServer` methods (notify, extranonce_subscribe, version_rolling_mask getters/setters)
//!
//! # Architecture
//!
//! ```text
//! ┌────────────────────────────────────────────────────────────┐
//! │                    stratum module                           │
//! │                                                            │
//! │  ┌──────────────┐         ┌──────────────────────┐       │
//! │  │   core.rs    │◄───────►│   sv1_compat.rs      │       │
//! │  │  (legacy)    │         │  (compatibility)     │       │
//! │  └──────────────┘         └──────────┬───────────┘       │
//! │                                      │                    │
//! │                                      ▼                    │
//! │                           ┌──────────────────┐           │
//! │                           │    sv1_api       │           │
//! │                           │  (standard SV1)  │           │
//! │                           └──────────────────┘           │
//! └────────────────────────────────────────────────────────────┘
//! ```

// Core Stratum implementation (original Braidpool code)
mod core;

// SV1 API compatibility layer
pub mod sv1_compat;

// SV1 API IsServer trait implementation
mod sv1_server_impl;

// Re-export core types for backward compatibility
pub use core::{
    reverse_four_byte_chunks, BlockSubmissionRequest, BlockTemplate, ConnectionInfo,
    ConnectionMapping, DownstreamClient, JobDetails, JobNotification, JobNotificationResponse,
    MiningJobMap, NotifyCmd, Notifier, Server, StandardRequest, StandardResponse,
    StratumResponses, StratumServerConfig, SuggestDifficultyResponse,
};

// Re-export SV1 compatibility utilities
pub use sv1_compat::{
    parse_sv1_message, sv1_message_to_braidpool_request, ConversionError, FromSv1, Sv1Message,
    ToSv1,
};
