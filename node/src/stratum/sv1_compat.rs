//! SV1 Protocol Compatibility Layer
//!
//! This module provides compatibility between Braidpool's internal types
//! and the official Stratum V1 API types from the `sv1_api` crate.
//!
//! # Purpose
//!
//! The `sv1_api` crate provides standardized types for the Stratum V1 protocol,
//! following the official specification. This module bridges Braidpool's existing
//! implementation with these standard types, enabling:
//!
//! - **Type Conversion**: Converting between Braidpool types and `sv1_api` types
//! - **Message Parsing**: Using `sv1_api` for JSON-RPC message parsing
//! - **Protocol Compliance**: Ensuring compatibility with standard SV1 miners
//! - **Gradual Migration**: Allowing incremental adoption of `sv1_api` types
//!
//! # Architecture
//!
//! ```text
//! ┌─────────────────────────────────────────────────────────────┐
//! │                    Braidpool Node                           │
//! │                                                             │
//! │  ┌──────────────┐          ┌─────────────────────────┐    │
//! │  │   stratum.rs │◄────────►│   sv1_compat.rs         │    │
//! │  │  (existing)  │          │  (compatibility layer)   │    │
//! │  └──────────────┘          └──────────┬──────────────┘    │
//! │                                       │                     │
//! │                                       ▼                     │
//! │                            ┌──────────────────┐            │
//! │                            │    sv1_api       │            │
//! │                            │  (standard SV1)  │            │
//! │                            └──────────────────┘            │
//! └─────────────────────────────────────────────────────────────┘
//! ```
//!
//! # Migration Strategy
//!
//! 1. **Phase 1**: Message parsing using `sv1_api::json_rpc::Message`
//! 2. **Phase 2**: Implement `IsServer` trait for `DownstreamClient`
//! 3. **Phase 3**: Replace custom types with `sv1_api` equivalents
//! 4. **Phase 4**: Remove compatibility layer once migration is complete
//!
//! # Related Issue
//!
//! GitHub Issue: [#313 - Migrate to SRI Stratum V1 crates](https://github.com/braidpool/braidpool/issues/313)

// Allow unused imports for now - they will be used as we implement the compatibility layer
#![allow(unused_imports)]

use sv1_api::{
    error::Error as Sv1Error,
    json_rpc::{Message, Notification, Response, StandardRequest as Sv1StandardRequest},
    methods::{
        client_to_server::{Authorize, Configure, Submit, Subscribe},
        server_to_client::{Notify, SetDifficulty, SetExtranonce, VersionRollingParams},
        Client2Server, Method, ParsingMethodError, Server2Client,
    },
    utils::{Extranonce as Sv1Extranonce, HexU32Be},
    ClientStatus, IsClient, IsServer,
};

// Re-export Braidpool's internal types for clarity
use super::core::{
    BlockSubmissionRequest, DownstreamClient, JobDetails, JobNotification, MiningJobMap,
    StandardRequest as BraidpoolStandardRequest, StandardResponse as BraidpoolStandardResponse,
    StratumResponses, StratumServerConfig,
};

// ============================================================================
// Type Aliases
// ============================================================================

/// Alias for SV1 API message type for clarity
pub type Sv1Message = Message;

/// Alias for SV1 API error type
pub type Sv1ApiError<'a> = Sv1Error<'a>;

// ============================================================================
// Message Conversion Traits
// ============================================================================

/// Trait for converting Braidpool types to SV1 API types
pub trait ToSv1 {
    /// The corresponding SV1 API type
    type Sv1Type;

    /// Convert this Braidpool type to its SV1 API equivalent
    fn to_sv1(&self) -> Self::Sv1Type;
}

/// Trait for converting SV1 API types to Braidpool types
pub trait FromSv1<T> {
    /// Convert from an SV1 API type to a Braidpool type
    ///
    /// # Errors
    ///
    /// Returns an error if the conversion is not possible (e.g., missing required fields)
    fn from_sv1(sv1: T) -> Result<Self, ConversionError>
    where
        Self: Sized;
}

// ============================================================================
// Error Types
// ============================================================================

/// Errors that can occur during type conversion
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ConversionError {
    /// Missing required field during conversion
    MissingField(&'static str),
    /// Invalid value for a field
    InvalidValue { field: &'static str, reason: String },
    /// Parsing error from sv1_api
    Sv1ParseError(String),
    /// General conversion error
    Other(String),
}

impl std::fmt::Display for ConversionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ConversionError::MissingField(field) => {
                write!(f, "Missing required field: {}", field)
            }
            ConversionError::InvalidValue { field, reason } => {
                write!(f, "Invalid value for field '{}': {}", field, reason)
            }
            ConversionError::Sv1ParseError(err) => {
                write!(f, "SV1 parsing error: {}", err)
            }
            ConversionError::Other(msg) => write!(f, "Conversion error: {}", msg),
        }
    }
}

impl std::error::Error for ConversionError {}

// ============================================================================
// StandardRequest Conversion
// ============================================================================

impl ToSv1 for BraidpoolStandardRequest {
    type Sv1Type = Sv1StandardRequest;

    fn to_sv1(&self) -> Self::Sv1Type {
        Sv1StandardRequest {
            id: self.id,
            method: self.method.clone(),
            params: self.params.clone(),
        }
    }
}

impl FromSv1<Sv1StandardRequest> for BraidpoolStandardRequest {
    fn from_sv1(sv1: Sv1StandardRequest) -> Result<Self, ConversionError> {
        Ok(BraidpoolStandardRequest {
            id: sv1.id,
            method: sv1.method,
            params: sv1.params,
        })
    }
}

// ============================================================================
// Standard Rust From/Into Trait Implementations for StandardRequest
// ============================================================================

/// Convert Braidpool StandardRequest to SV1 API StandardRequest
impl From<BraidpoolStandardRequest> for Sv1StandardRequest {
    fn from(braidpool: BraidpoolStandardRequest) -> Self {
        Sv1StandardRequest {
            id: braidpool.id,
            method: braidpool.method,
            params: braidpool.params,
        }
    }
}

/// Convert SV1 API StandardRequest to Braidpool StandardRequest
impl From<Sv1StandardRequest> for BraidpoolStandardRequest {
    fn from(sv1: Sv1StandardRequest) -> Self {
        BraidpoolStandardRequest {
            id: sv1.id,
            method: sv1.method,
            params: sv1.params,
        }
    }
}

// ============================================================================
// StandardResponse Conversion
// ============================================================================

impl ToSv1 for BraidpoolStandardResponse {
    type Sv1Type = Response;

    fn to_sv1(&self) -> Self::Sv1Type {
        Response {
            id: self.id.unwrap_or(0),
            error: self
                .error
                .as_ref()
                .map(|e| sv1_api::json_rpc::JsonRpcError {
                    code: 20, // Generic stratum error code
                    message: e.clone(),
                    data: None,
                }),
            result: self.result.clone().unwrap_or(serde_json::Value::Null),
        }
    }
}

impl FromSv1<Response> for BraidpoolStandardResponse {
    fn from_sv1(sv1: Response) -> Result<Self, ConversionError> {
        Ok(BraidpoolStandardResponse {
            id: Some(sv1.id),
            result: Some(sv1.result),
            error: sv1.error.map(|e| e.message),
        })
    }
}

/// Convert Braidpool StandardResponse to SV1 API Response
impl From<BraidpoolStandardResponse> for Response {
    fn from(braidpool: BraidpoolStandardResponse) -> Self {
        Response {
            id: braidpool.id.unwrap_or(0),
            error: braidpool
                .error
                .as_ref()
                .map(|e| sv1_api::json_rpc::JsonRpcError {
                    code: 20, // Generic stratum error code
                    message: e.clone(),
                    data: None,
                }),
            result: braidpool.result.unwrap_or(serde_json::Value::Null),
        }
    }
}

/// Convert SV1 API Response to Braidpool StandardResponse
impl From<Response> for BraidpoolStandardResponse {
    fn from(sv1: Response) -> Self {
        BraidpoolStandardResponse {
            id: Some(sv1.id),
            result: Some(sv1.result),
            error: sv1.error.map(|e| e.message),
        }
    }
}

// ============================================================================
// Message Parsing Utilities
// ============================================================================

/// Parse a JSON-RPC message string using sv1_api
///
/// This is the primary entry point for parsing incoming Stratum V1 messages
/// from miners.
///
/// # Arguments
///
/// * `json_str` - Raw JSON string from the miner
///
/// # Returns
///
/// Returns a parsed `sv1_api::json_rpc::Message` which can be:
/// - `Message::StandardRequest` - Request expecting a response
/// - `Message::Notification` - One-way notification (no response expected)
/// - `Message::OkResponse` / `Message::ErrorResponse` - Responses from server
///
/// # Example
///
/// ```ignore
/// let json = r#"{"id":1,"method":"mining.subscribe","params":[]}"#;
/// let message = parse_sv1_message(json)?;
/// ```
pub fn parse_sv1_message(json_str: &str) -> Result<Sv1Message, ConversionError> {
    serde_json::from_str::<Sv1Message>(json_str)
        .map_err(|e| ConversionError::Sv1ParseError(e.to_string()))
}

/// Convert a parsed SV1 message into a Braidpool StandardRequest
///
/// This helper extracts the request data from an `sv1_api::Message` and
/// converts it to Braidpool's internal `StandardRequest` type.
///
/// # Arguments
///
/// * `message` - Parsed SV1 message
///
/// # Returns
///
/// Returns `Some(StandardRequest)` if the message is a request, `None` otherwise
pub fn sv1_message_to_braidpool_request(message: &Sv1Message) -> Option<BraidpoolStandardRequest> {
    match message {
        Message::StandardRequest(req) => {
            Some(BraidpoolStandardRequest::from_sv1(req.clone()).ok()?)
        }
        _ => None,
    }
}

// ============================================================================
// TODO: Future Conversions
// ============================================================================

// TODO: Implement JobNotification <-> sv1_api::server_to_client::Notify
// TODO: Implement DownstreamClient IsServer trait
// TODO: Implement extranonce conversion helpers
// TODO: Implement difficulty conversion helpers
// TODO: Implement version rolling mask conversions

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_subscribe_request() {
        let json = r#"{"id":1,"method":"mining.subscribe","params":[]}"#;
        let message = parse_sv1_message(json);
        assert!(message.is_ok());

        if let Ok(Message::StandardRequest(req)) = message {
            assert_eq!(req.method, "mining.subscribe");
            assert_eq!(req.id, 1);
        } else {
            panic!("Expected StandardRequest");
        }
    }

    #[test]
    fn test_braidpool_to_sv1_request_conversion() {
        let braidpool_req = BraidpoolStandardRequest {
            id: 42,
            method: "mining.authorize".to_string(),
            params: serde_json::json!(["user", "pass"]),
        };

        let sv1_req = braidpool_req.to_sv1();
        assert_eq!(sv1_req.id, 42);
        assert_eq!(sv1_req.method, "mining.authorize");
    }

    #[test]
    fn test_sv1_to_braidpool_request_conversion() {
        let sv1_req = Sv1StandardRequest {
            id: 100,
            method: "mining.submit".to_string(),
            params: serde_json::json!([]),
        };

        let braidpool_req = BraidpoolStandardRequest::from_sv1(sv1_req);
        assert!(braidpool_req.is_ok());

        let req = braidpool_req.unwrap();
        assert_eq!(req.id, 100);
        assert_eq!(req.method, "mining.submit");
    }

    #[test]
    fn test_parse_invalid_json() {
        let invalid_json = r#"{"id":1,"method":"mining.subscribe""#; // missing closing brace
        let result = parse_sv1_message(invalid_json);
        assert!(result.is_err());
    }

    #[test]
    fn test_sv1_message_to_braidpool_request() {
        let json = r#"{"id":1,"method":"mining.configure","params":[]}"#;
        let message = parse_sv1_message(json).unwrap();
        let braidpool_req = sv1_message_to_braidpool_request(&message);

        assert!(braidpool_req.is_some());
        let req = braidpool_req.unwrap();
        assert_eq!(req.method, "mining.configure");
    }

    // ========================================================================
    // Tests for Standard Rust From/Into Traits
    // ========================================================================

    #[test]
    fn test_from_trait_braidpool_request_to_sv1() {
        let braidpool_req = BraidpoolStandardRequest {
            id: 99,
            method: "mining.subscribe".to_string(),
            params: serde_json::json!(["agent", null]),
        };

        // Use From trait
        let sv1_req: Sv1StandardRequest = braidpool_req.clone().into();
        assert_eq!(sv1_req.id, 99);
        assert_eq!(sv1_req.method, "mining.subscribe");
        assert_eq!(sv1_req.params, serde_json::json!(["agent", null]));
    }

    #[test]
    fn test_from_trait_sv1_request_to_braidpool() {
        let sv1_req = Sv1StandardRequest {
            id: 88,
            method: "mining.authorize".to_string(),
            params: serde_json::json!(["worker", "password"]),
        };

        // Use From trait
        let braidpool_req: BraidpoolStandardRequest = sv1_req.into();
        assert_eq!(braidpool_req.id, 88);
        assert_eq!(braidpool_req.method, "mining.authorize");
    }

    #[test]
    fn test_into_trait_request_conversion() {
        let braidpool_req = BraidpoolStandardRequest {
            id: 77,
            method: "mining.submit".to_string(),
            params: serde_json::json!([]),
        };

        // Use Into trait (automatic from From implementation)
        let sv1_req: Sv1StandardRequest = braidpool_req.into();
        assert_eq!(sv1_req.id, 77);
        assert_eq!(sv1_req.method, "mining.submit");
    }

    // ========================================================================
    // Tests for StandardResponse Conversions
    // ========================================================================

    #[test]
    fn test_braidpool_response_to_sv1_success() {
        let braidpool_resp = BraidpoolStandardResponse {
            id: Some(42),
            result: Some(serde_json::json!(true)),
            error: None,
        };

        let sv1_resp = braidpool_resp.to_sv1();
        assert_eq!(sv1_resp.id, 42);
        assert_eq!(sv1_resp.result, serde_json::json!(true));
        assert!(sv1_resp.error.is_none());
    }

    #[test]
    fn test_braidpool_response_to_sv1_error() {
        let braidpool_resp = BraidpoolStandardResponse {
            id: Some(10),
            result: Some(serde_json::Value::Null),
            error: Some("Unauthorized".to_string()),
        };

        let sv1_resp = braidpool_resp.to_sv1();
        assert_eq!(sv1_resp.id, 10);
        assert!(sv1_resp.error.is_some());
        let error = sv1_resp.error.unwrap();
        assert_eq!(error.message, "Unauthorized");
        assert_eq!(error.code, 20);
    }

    #[test]
    fn test_sv1_response_to_braidpool() {
        let sv1_resp = Response {
            id: 55,
            result: serde_json::json!({"status": "ok"}),
            error: None,
        };

        let braidpool_resp = BraidpoolStandardResponse::from_sv1(sv1_resp).unwrap();
        assert_eq!(braidpool_resp.id, Some(55));
        assert_eq!(
            braidpool_resp.result,
            Some(serde_json::json!({"status": "ok"}))
        );
        assert!(braidpool_resp.error.is_none());
    }

    #[test]
    fn test_from_trait_braidpool_response_to_sv1() {
        let braidpool_resp = BraidpoolStandardResponse {
            id: Some(33),
            result: Some(serde_json::json!(["result1", "result2"])),
            error: None,
        };

        // Use From trait
        let sv1_resp: Response = braidpool_resp.into();
        assert_eq!(sv1_resp.id, 33);
        assert_eq!(sv1_resp.result, serde_json::json!(["result1", "result2"]));
        assert!(sv1_resp.error.is_none());
    }

    #[test]
    fn test_from_trait_sv1_response_to_braidpool() {
        let sv1_resp = Response {
            id: 44,
            result: serde_json::json!(null),
            error: Some(sv1_api::json_rpc::JsonRpcError {
                code: 25,
                message: "Job not found".to_string(),
                data: None,
            }),
        };

        // Use From trait
        let braidpool_resp: BraidpoolStandardResponse = sv1_resp.into();
        assert_eq!(braidpool_resp.id, Some(44));
        assert_eq!(braidpool_resp.error, Some("Job not found".to_string()));
    }

    #[test]
    fn test_response_with_none_id() {
        let braidpool_resp = BraidpoolStandardResponse {
            id: None,
            result: Some(serde_json::json!(true)),
            error: None,
        };

        // When id is None, should default to 0
        let sv1_resp: Response = braidpool_resp.into();
        assert_eq!(sv1_resp.id, 0);
    }

    #[test]
    fn test_response_with_none_result() {
        let braidpool_resp = BraidpoolStandardResponse {
            id: Some(66),
            result: None,
            error: None,
        };

        // When result is None, should default to null
        let sv1_resp: Response = braidpool_resp.into();
        assert_eq!(sv1_resp.result, serde_json::Value::Null);
    }

    #[test]
    fn test_bidirectional_request_conversion() {
        let original = BraidpoolStandardRequest {
            id: 123,
            method: "mining.configure".to_string(),
            params: serde_json::json!({"version_rolling": true}),
        };

        // Convert to SV1 and back
        let sv1: Sv1StandardRequest = original.clone().into();
        let converted_back: BraidpoolStandardRequest = sv1.into();

        assert_eq!(original.id, converted_back.id);
        assert_eq!(original.method, converted_back.method);
        assert_eq!(original.params, converted_back.params);
    }

    #[test]
    fn test_bidirectional_response_conversion() {
        let original = BraidpoolStandardResponse {
            id: Some(456),
            result: Some(serde_json::json!({"subscribed": true})),
            error: None,
        };

        // Convert to SV1 and back
        let sv1: Response = original.clone().into();
        let converted_back: BraidpoolStandardResponse = sv1.into();

        assert_eq!(original.id, converted_back.id);
        assert_eq!(original.result, converted_back.result);
        assert_eq!(original.error, converted_back.error);
    }
}
