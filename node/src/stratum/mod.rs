//! Stratum V1 and V2 Protocol Implementation for Braidpool
//!
//! This module implements both Stratum V1 and Stratum V2 mining protocols,
//! providing compatibility with standard miners and advanced SV2 features.
//!
//! # Module Structure
//!
//! ## Stratum V1 (Legacy)
//! - `core` - Core Stratum implementation (original braidpool code)
//! - `sv1_compat` - Compatibility layer with official `sv1_api` types
//! - `sv1_server_impl` - Implementation of `sv1_api::IsServer` trait
//!
//! ## Stratum V2 (New)
//! - `sv2_server` - Stratum V2 server implementation using SRI crates
//!
//! # Migration Status (Issue #313)
//!
//! This module implements both SV1 and SV2 protocols using official crates from
//! the Stratum Reference Implementation (SRI) project.
//!
//! **SV1 Status (Complete):**
//! - ✅ `sv1_api` dependency added
//! - ✅ Compatibility layer created
//! - ✅ `IsServer` trait implemented
//! - ✅ Type conversion implementation (From/Into traits)
//! - ✅ Message parsing using `sv1_api::json_rpc::Message`
//! - ✅ All core handlers (configure, subscribe, authorize, submit)
//!
//! **SV2 Status (In Progress):**
//! - ✅ SV2 crate dependencies added (mining_sv2, codec_sv2, framing_sv2, etc.)
//! - ✅ Basic SV2 server structure created
//! - ✅ Extended Channels support (OpenChannel, SubmitShares)
//! - ✅ Standard Channels support (OpenChannel, SubmitShares)
//! - ⏳ Future Jobs implementation
//! - ⏳ Connection handling and message routing
//! - ⏳ Integration with Braidpool's block submission pipeline
//!
//! # Architecture
//!
//! ```text
//! ┌────────────────────────────────────────────────────────────────┐
//! │                     stratum module                              │
//! │                                                                 │
//! │  ┌──────────────┐         ┌──────────────────────┐            │
//! │  │   core.rs    │◄───────►│   sv1_compat.rs      │            │
//! │  │  (legacy)    │         │  (compatibility)     │            │
//! │  └──────────────┘         └──────────┬───────────┘            │
//! │                                      │                         │
//! │                                      ▼                         │
//! │                           ┌──────────────────┐                │
//! │                           │    sv1_api       │                │
//! │                           │  (standard SV1)  │                │
//! │                           └──────────────────┘                │
//! │                                                                │
//! │  ┌──────────────────────────────────────────────────┐        │
//! │  │              sv2_server.rs                       │        │
//! │  │  (Extended Channels, Standard Channels,          │        │
//! │  │   Future Jobs, Native SV2 communication)         │        │
//! │  │                                                  │        │
//! │  │   Uses: mining_sv2, codec_sv2, framing_sv2,     │        │
//! │  │         common_messages_sv2, const_sv2           │        │
//! │  └──────────────────────────────────────────────────┘        │
//! └────────────────────────────────────────────────────────────────┘
//! ```

// Core Stratum implementation (original Braidpool code)
mod core;

// SV1 API compatibility layer
pub mod sv1_compat;

// SV1 API IsServer trait implementation
mod sv1_server_impl;

// SV2 server implementation
pub mod sv2_server;

// Re-export core types for backward compatibility
pub use core::{
    reverse_four_byte_chunks, BlockSubmissionRequest, BlockTemplate, ConnectionInfo,
    ConnectionMapping, DownstreamClient, JobDetails, JobNotification, JobNotificationResponse,
    MiningJobMap, Notifier, NotifyCmd, Server, StandardRequest, StandardResponse, StratumResponses,
    StratumServerConfig, SuggestDifficultyResponse,
};

// Re-export SV1 compatibility utilities
pub use sv1_compat::{
    parse_sv1_message, sv1_message_to_braidpool_request, ConversionError, FromSv1, Sv1Message,
    ToSv1,
};
