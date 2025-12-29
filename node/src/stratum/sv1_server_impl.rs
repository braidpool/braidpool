//! Implementation of `sv1_api::IsServer` trait for `DownstreamClient`
//!
//! This module bridges Braidpool's `DownstreamClient` with the standard
//! Stratum V1 server interface defined by `sv1_api`.
//!
//! # Architecture
//!
//! The `IsServer` trait provides a standard interface for handling Stratum V1
//! client messages. By implementing this trait, `DownstreamClient` can:
//!
//! - Parse incoming messages using `sv1_api` types
//! - Handle standard methods (subscribe, authorize, configure, submit)
//! - Manage extranonce allocation
//! - Support version rolling for overt ASICBOOST
//!
//! # Implementation Status
//!
//! Currently, all methods are implemented as placeholders using `todo!()`.
//! They will be incrementally implemented to integrate with Braidpool's
//! existing functionality.
//!
//! # Related
//!
//! - Issue #313: Migrate to SRI Stratum V1 crates
//! - See `sv1_compat.rs` for type conversions

use sv1_api::{
    error::Error as Sv1Error,
    json_rpc,
    methods::{client_to_server, server_to_client},
    utils::{Extranonce as Sv1Extranonce, HexU32Be},
    IsServer,
};
use tracing::debug;

use super::core::DownstreamClient;

// ============================================================================
// IsServer Trait Implementation
// ============================================================================

impl<'a> IsServer<'a> for DownstreamClient {
    // ------------------------------------------------------------------------
    // Configure Handler
    // ------------------------------------------------------------------------

    /// Handle mining.configure request
    ///
    /// This is typically the first message sent by miners that support
    /// version rolling (ASICBOOST).
    ///
    /// # Arguments
    ///
    /// * `request` - Configure request from the miner
    ///
    /// # Returns
    ///
    /// A tuple of:
    /// - `Option<VersionRollingParams>` - Version rolling parameters if supported
    /// - `Option<bool>` - Whether minimum difficulty is supported
    fn handle_configure(
        &mut self,
        request: &client_to_server::Configure,
    ) -> (
        Option<server_to_client::VersionRollingParams>,
        Option<bool>,
    ) {
        // Extract version rolling mask from request
        let requested_mask = request.version_rolling_mask();
        let requested_min_bit_count = request.version_rolling_min_bit_count();

        let version_rolling_params = if requested_mask.is_some() {
            // Get the requested mask or use default
            let mask = requested_mask.unwrap_or(HexU32Be(0x1FFFE000));

            // Intersect with pool's allowed bits (0x1FFFE000 is reasonable default)
            // This allows all 16 version bits to be used
            let final_mask = HexU32Be(mask.0 & 0x1FFFE000);

            // Store mask in DownstreamClient for future use
            self.version_rolling_mask = Some(format!("{:08x}", final_mask.0));

            // Store min bit count if provided (check and store first)
            // Note: sv1_api returns Some(HexU32Be(0)) when min_bit_count is None,
            // so we need to check for non-zero values to determine if it was actually provided
            if let Some(min_bit) = requested_min_bit_count {
                // Only store if it's a meaningful value (non-zero)
                if min_bit.0 != 0 {
                    self.version_rolling_min_bit = Some(min_bit.0);
                }

                // Build response parameters with the provided/default min bit count
                Some(server_to_client::VersionRollingParams {
                    version_rolling: true,
                    version_rolling_mask: final_mask,
                    version_rolling_min_bit_count: min_bit,
                })
            } else {
                // Build response parameters with default min bit count
                Some(server_to_client::VersionRollingParams {
                    version_rolling: true,
                    version_rolling_mask: final_mask,
                    version_rolling_min_bit_count: HexU32Be(0),
                })
            }
        } else {
            None
        };

        // Mark channel as configured
        self.channel_configured = true;

        // Return version rolling params and minimum difficulty support (false - not supported)
        (version_rolling_params, Some(false))
    }

    // ------------------------------------------------------------------------
    // Subscribe Handler
    // ------------------------------------------------------------------------

    /// Handle mining.subscribe request
    ///
    /// Subscribes the miner to receive mining jobs. Returns subscription
    /// details that the miner can use to identify the connection.
    ///
    /// # Arguments
    ///
    /// * `request` - Subscribe request from the miner
    ///
    /// # Returns
    ///
    /// A vector of (subscription_id, subscription_type) tuples.
    /// Typically: `[("mining.notify", "unique_id"), ("mining.set_difficulty", "unique_id")]`
    fn handle_subscribe(&self, _request: &client_to_server::Subscribe) -> Vec<(String, String)> {
        // Return standard subscription IDs
        // Note: These are dummy values matching the legacy implementation
        // TODO: Generate truly unique subscription IDs based on connection_id
        vec![
            (String::from("mining.set_difficulty"), String::from("34")),
            (String::from("mining.notify"), String::from("12")),
        ]
    }

    // ------------------------------------------------------------------------
    // Authorize Handler
    // ------------------------------------------------------------------------

    /// Handle mining.authorize request
    ///
    /// Authenticates a worker. Multiple workers can be authorized on the
    /// same connection.
    ///
    /// # Arguments
    ///
    /// * `request` - Authorize request containing username and password
    ///
    /// # Returns
    ///
    /// `true` if authorization succeeds, `false` otherwise
    ///
    /// # Note
    ///
    /// Currently accepts all authorization requests (no validation).
    /// In production, this should validate credentials against a database or service.
    fn handle_authorize(&self, _request: &client_to_server::Authorize) -> bool {
        // Currently accepts all authorization requests
        // TODO: Implement actual credential validation
        true
    }

    // ------------------------------------------------------------------------
    // Submit Handler
    // ------------------------------------------------------------------------

    /// Handle mining.submit request
    ///
    /// Processes a share submission from the miner. Validates the share
    /// and forwards it to the pool.
    ///
    /// # Arguments
    ///
    /// * `request` - Submit request containing share data
    ///
    /// # Returns
    ///
    /// `true` if the share is accepted, `false` if rejected
    ///
    /// # TODO
    ///
    /// - Map to existing `handle_submit` in DownstreamClient
    /// - Validate share (job_id, extranonce, ntime, nonce)
    /// - Check difficulty target
    /// - Submit valid shares to Braidpool
    ///
    /// # Implementation Note
    ///
    /// This is a simplified implementation that accepts all submissions.
    /// The full validation logic (coinbase reconstruction, merkle root calculation,
    /// PoW validation, and block submission) is still handled by `handle_submit_legacy`
    /// which is called from the request routing logic in `core.rs`.
    ///
    /// The trait's `handle_submit` is meant to be a simple validation layer, but
    /// Braidpool's architecture requires complex async operations with access to:
    /// - `Arc<Mutex<MiningJobMap>>` for job lookup
    /// - `Arc<Mutex<SwarmHandler>>` for block propagation
    /// - Database for share storage
    ///
    /// Future work (after complete migration to sv1_api) should refactor the architecture
    /// to make these dependencies available through the trait interface, or restructure
    /// the validation flow to separate concerns:
    /// 1. Simple validation in `handle_submit` (job exists, extranonce valid, etc.)
    /// 2. Complex async operations in a separate layer
    ///
    /// For now, this method returns `true` to indicate acceptance, while the actual
    /// validation continues to happen in `handle_submit_legacy`.
    fn handle_submit(&self, request: &client_to_server::Submit<'a>) -> bool {
        // Log the submission for debugging
        debug!(
            job_id = %request.job_id,
            user = %request.user_name,
            nonce = %format!("{:08x}", request.nonce.0),
            time = %format!("{:08x}", request.time.0),
            "Received share submission via sv1_api trait"
        );

        // For now, accept all submissions
        // The actual validation happens in handle_submit_legacy
        true
    }

    // ------------------------------------------------------------------------
    // Extranonce Subscribe Handler
    // ------------------------------------------------------------------------

    /// Handle mining.extranonce.subscribe notification
    ///
    /// Indicates the miner supports dynamic extranonce updates.
    ///
    /// # TODO
    ///
    /// - Map to existing `handle_extranonce_subscribe`
    /// - Mark connection as supporting dynamic extranonce
    fn handle_extranonce_subscribe(&self) {
        todo!("Implement handle_extranonce_subscribe")
    }

    // ------------------------------------------------------------------------
    // Authorization Check
    // ------------------------------------------------------------------------

    /// Check if a worker name is authorized
    ///
    /// # Arguments
    ///
    /// * `name` - Worker name to check (currently unused)
    ///
    /// # Returns
    ///
    /// `true` if the connection is authorized, `false` otherwise
    ///
    /// # Note
    ///
    /// Currently checks the connection-level authorization flag.
    /// In a production system, this should check per-worker authorization.
    fn is_authorized(&self, _name: &str) -> bool {
        self.authorized
    }

    // ------------------------------------------------------------------------
    // Authorize Worker
    // ------------------------------------------------------------------------

    /// Mark a worker as authorized
    ///
    /// # Arguments
    ///
    /// * `name` - Worker name to authorize (currently unused)
    ///
    /// # Note
    ///
    /// Currently sets the connection-level authorization flag.
    /// In a production system, this should track individual worker authorizations.
    fn authorize(&mut self, _name: &str) {
        self.authorized = true;
    }

    // ------------------------------------------------------------------------
    // Extranonce1 Management
    // ------------------------------------------------------------------------

    /// Set or generate extranonce1 for this connection
    ///
    /// # Arguments
    ///
    /// * `extranonce1` - Optional extranonce1 to set. If None, use existing one
    ///
    /// # Returns
    ///
    /// The extranonce1 that was set or the existing one
    fn set_extranonce1(&mut self, extranonce1: Option<Sv1Extranonce<'a>>) -> Sv1Extranonce<'a> {
        if let Some(new_extranonce) = extranonce1 {
            // Convert Sv1Extranonce to Vec<u8> and store
            self.extranonce1 = new_extranonce.0.inner_as_ref().to_vec();
        }

        // Return the current extranonce1 (either newly set or existing)
        // Convert Vec<u8> to Sv1Extranonce
        Sv1Extranonce::try_from(self.extranonce1.clone())
            .expect("extranonce1 should always be valid")
    }

    /// Get the current extranonce1 for this connection
    ///
    /// # Returns
    ///
    /// The current extranonce1 as sv1_api::Extranonce
    fn extranonce1(&self) -> Sv1Extranonce<'a> {
        // Convert Vec<u8> to Sv1Extranonce
        Sv1Extranonce::try_from(self.extranonce1.clone())
            .expect("extranonce1 should always be valid")
    }

    // ------------------------------------------------------------------------
    // Extranonce2 Size Management
    // ------------------------------------------------------------------------

    /// Set or use default extranonce2 size
    ///
    /// # Arguments
    ///
    /// * `extra_nonce2_size` - Optional size to set. If None, keep current value
    ///
    /// # Returns
    ///
    /// The extranonce2 size that was set or the current value
    fn set_extranonce2_size(&mut self, extra_nonce2_size: Option<usize>) -> usize {
        if let Some(size) = extra_nonce2_size {
            self.extranonce2_len = size;
        }
        self.extranonce2_len
    }

    /// Get the current extranonce2 size
    ///
    /// # Returns
    ///
    /// The current extranonce2 size
    fn extranonce2_size(&self) -> usize {
        self.extranonce2_len
    }

    // ------------------------------------------------------------------------
    // Version Rolling Support
    // ------------------------------------------------------------------------

    /// Get the version rolling mask
    ///
    /// Used for overt ASICBOOST support.
    ///
    /// # Returns
    ///
    /// The version rolling mask if configured, None otherwise
    ///
    /// # TODO
    ///
    /// - Convert from DownstreamClient.version_rolling_mask (Option<String>)
    /// - Parse as HexU32Be
    fn version_rolling_mask(&self) -> Option<HexU32Be> {
        todo!("Implement version_rolling_mask - convert from DownstreamClient")
    }

    /// Set the version rolling mask
    ///
    /// # Arguments
    ///
    /// * `mask` - The version rolling mask to set
    ///
    /// # TODO
    ///
    /// - Convert HexU32Be to String
    /// - Store in DownstreamClient.version_rolling_mask
    fn set_version_rolling_mask(&mut self, _mask: Option<HexU32Be>) {
        todo!("Implement set_version_rolling_mask - store in DownstreamClient")
    }

    /// Set the minimum version rolling bit count
    ///
    /// # Arguments
    ///
    /// * `mask` - The minimum bit count
    ///
    /// # TODO
    ///
    /// - Store in DownstreamClient.version_rolling_min_bit
    fn set_version_rolling_min_bit(&mut self, _mask: Option<HexU32Be>) {
        todo!("Implement set_version_rolling_min_bit - store in DownstreamClient")
    }

    // ------------------------------------------------------------------------
    // Notify (Send Mining Job)
    // ------------------------------------------------------------------------

    /// Generate a mining.notify message for this connection
    ///
    /// Sends a new mining job to the miner.
    ///
    /// # Returns
    ///
    /// A JSON-RPC notification message containing the mining job
    ///
    /// # TODO
    ///
    /// - Get latest job from MiningJobMap
    /// - Convert JobNotification to sv1_api::server_to_client::Notify
    /// - Construct json_rpc::Message
    fn notify(&mut self) -> Result<json_rpc::Message, Sv1Error<'_>> {
        todo!("Implement notify - convert JobNotification to sv1_api::Notify")
    }

    // ------------------------------------------------------------------------
    // Optional Methods with Default Implementations
    // ------------------------------------------------------------------------

    // Note: The following methods have default implementations in the trait:
    // - handle_message() - Routes messages to appropriate handlers
    // - handle_request() - Processes Client2Server methods
    // - update_extranonce() - Sends mining.set_extranonce
    // - handle_set_difficulty() - Sends mining.set_difficulty
}

// ============================================================================
// Helper Functions
// ============================================================================

// TODO: Add helper functions for type conversions:
// - convert_extranonce_to_sv1()
// - convert_extranonce_from_sv1()
// - convert_hex_u32_be_to_string()
// - convert_string_to_hex_u32_be()
// - convert_job_notification_to_notify()

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use sv1_api::methods::client_to_server::Configure;

    #[test]
    fn test_handle_configure_with_version_rolling() {
        // Create a DownstreamClient with default values
        let mut client = DownstreamClient::default();

        // Create a configure request with version rolling
        let configure = Configure::new(
            1,
            Some(HexU32Be(0xFFFFFFFF)), // Request full mask
            Some(HexU32Be(16)),          // Request 16 bits
        );

        // Handle the configure request
        let (version_rolling, min_difficulty) = client.handle_configure(&configure);

        // Verify response
        assert!(version_rolling.is_some());
        let vr = version_rolling.unwrap();
        assert!(vr.version_rolling);
        // The mask should be intersected with 0x1FFFE000
        assert_eq!(vr.version_rolling_mask.0, 0x1FFFE000);
        assert_eq!(vr.version_rolling_min_bit_count.0, 16);

        // Verify minimum difficulty is not supported
        assert_eq!(min_difficulty, Some(false));

        // Verify client state was updated
        assert!(client.channel_configured);
        assert_eq!(client.version_rolling_mask, Some("1fffe000".to_string()));
        assert_eq!(client.version_rolling_min_bit, Some(16));
    }

    #[test]
    fn test_handle_configure_without_version_rolling() {
        // Create a DownstreamClient with default values
        let mut client = DownstreamClient::default();

        // Create a configure request without version rolling
        let configure = Configure::void(1);

        // Handle the configure request
        let (version_rolling, min_difficulty) = client.handle_configure(&configure);

        // Verify response
        assert!(version_rolling.is_none());
        assert_eq!(min_difficulty, Some(false));

        // Verify client state was updated
        assert!(client.channel_configured);
    }

    #[test]
    fn test_handle_configure_with_default_mask() {
        // Create a DownstreamClient with default values
        let mut client = DownstreamClient::default();

        // Create a configure request with mask but no min bit count
        let configure = Configure::new(
            1,
            Some(HexU32Be(0x1FFFE000)), // Use default mask
            None,                        // No min bit count
        );

        // Handle the configure request
        let (version_rolling, _) = client.handle_configure(&configure);

        // Verify response
        assert!(version_rolling.is_some());
        let vr = version_rolling.unwrap();
        assert_eq!(vr.version_rolling_mask.0, 0x1FFFE000);
        // When no min bit count is provided, response should have default 0
        assert_eq!(vr.version_rolling_min_bit_count.0, 0);

        // Verify client state
        assert_eq!(client.version_rolling_mask, Some("1fffe000".to_string()));
        // Client should not store min_bit when None is provided
        assert_eq!(client.version_rolling_min_bit, None);
    }

    #[test]
    fn test_handle_configure_mask_intersection() {
        // Create a DownstreamClient with default values
        let mut client = DownstreamClient::default();

        // Create a configure request with a mask that includes bits outside the allowed range
        let configure = Configure::new(
            1,
            Some(HexU32Be(0xFFFFFFFF)), // Full mask
            Some(HexU32Be(8)),
        );

        // Handle the configure request
        let (version_rolling, _) = client.handle_configure(&configure);

        // Verify the mask was properly intersected
        assert!(version_rolling.is_some());
        let vr = version_rolling.unwrap();
        // Should only include bits from 0x1FFFE000
        assert_eq!(vr.version_rolling_mask.0, 0x1FFFE000);
    }

    // ========================================================================
    // Tests for handle_subscribe
    // ========================================================================

    #[test]
    fn test_handle_subscribe_basic() {
        use sv1_api::methods::client_to_server::Subscribe;

        // Create a DownstreamClient with default values
        let client = DownstreamClient::default();

        // Create a subscribe request
        let subscribe = Subscribe {
            id: 1,
            agent_signature: "test_miner/1.0".to_string(),
            extranonce1: None,
        };

        // Handle the subscribe request
        let subscriptions = client.handle_subscribe(&subscribe);

        // Verify subscriptions
        assert_eq!(subscriptions.len(), 2);
        assert!(subscriptions.contains(&("mining.set_difficulty".to_string(), "34".to_string())));
        assert!(subscriptions.contains(&("mining.notify".to_string(), "12".to_string())));
    }

    #[test]
    fn test_extranonce1_get() {
        // Create a DownstreamClient with default values
        let client = DownstreamClient::default();

        // Get extranonce1
        let extranonce1 = client.extranonce1();

        // Verify it matches the internal value
        assert_eq!(extranonce1.0.inner_as_ref(), client.extranonce1.as_slice());
    }

    #[test]
    fn test_extranonce1_set() {
        use sv1_api::utils::Extranonce;

        // Create a DownstreamClient with default values
        let mut client = DownstreamClient::default();

        // Create a new extranonce1
        let new_extranonce_bytes = vec![0x11, 0x22, 0x33, 0x44];
        let new_extranonce = Extranonce::try_from(new_extranonce_bytes.clone()).unwrap();

        // Set the new extranonce1
        let result = client.set_extranonce1(Some(new_extranonce));

        // Verify it was set correctly
        assert_eq!(result.0.inner_as_ref(), new_extranonce_bytes.as_slice());
        assert_eq!(client.extranonce1, new_extranonce_bytes);
    }

    #[test]
    fn test_extranonce1_set_none() {
        // Create a DownstreamClient with default values
        let mut client = DownstreamClient::default();
        let original_extranonce = client.extranonce1.clone();

        // Set None (should keep existing value)
        let result = client.set_extranonce1(None);

        // Verify it kept the original value
        assert_eq!(result.0.inner_as_ref(), original_extranonce.as_slice());
        assert_eq!(client.extranonce1, original_extranonce);
    }

    #[test]
    fn test_extranonce2_size_get() {
        // Create a DownstreamClient with default values
        let client = DownstreamClient::default();

        // Get extranonce2 size
        let size = client.extranonce2_size();

        // Verify it matches the internal value
        assert_eq!(size, client.extranonce2_len);
    }

    #[test]
    fn test_extranonce2_size_set() {
        // Create a DownstreamClient with default values
        let mut client = DownstreamClient::default();

        // Set new extranonce2 size
        let new_size = 8;
        let result = client.set_extranonce2_size(Some(new_size));

        // Verify it was set correctly
        assert_eq!(result, new_size);
        assert_eq!(client.extranonce2_len, new_size);
    }

    #[test]
    fn test_extranonce2_size_set_none() {
        // Create a DownstreamClient with default values
        let mut client = DownstreamClient::default();
        let original_size = client.extranonce2_len;

        // Set None (should keep existing value)
        let result = client.set_extranonce2_size(None);

        // Verify it kept the original value
        assert_eq!(result, original_size);
        assert_eq!(client.extranonce2_len, original_size);
    }

    // ========================================================================
    // Tests for handle_authorize and authorization methods
    // ========================================================================

    #[test]
    fn test_handle_authorize_accepts_all() {
        use sv1_api::methods::client_to_server::Authorize;

        // Create a DownstreamClient with default values
        let client = DownstreamClient::default();

        // Create an authorize request
        let authorize = Authorize {
            id: 1,
            name: "worker1".to_string(),
            password: "password123".to_string(),
        };

        // Handle the authorize request
        let result = client.handle_authorize(&authorize);

        // Should always return true (accepts all)
        assert!(result);
    }

    #[test]
    fn test_is_authorized_initially_false() {
        // Create a DownstreamClient with default values
        let client = DownstreamClient::default();

        // Check authorization status
        let is_auth = client.is_authorized("worker1");

        // Should be false initially
        assert!(!is_auth);
    }

    #[test]
    fn test_authorize_sets_flag() {
        // Create a DownstreamClient with default values
        let mut client = DownstreamClient::default();

        // Verify initially not authorized
        assert!(!client.is_authorized("worker1"));

        // Authorize the worker
        client.authorize("worker1");

        // Verify now authorized
        assert!(client.is_authorized("worker1"));
        assert!(client.authorized);
    }

    #[test]
    fn test_authorize_multiple_workers() {
        // Create a DownstreamClient with default values
        let mut client = DownstreamClient::default();

        // Authorize first worker
        client.authorize("worker1");
        assert!(client.is_authorized("worker1"));

        // Authorize second worker (currently same flag)
        client.authorize("worker2");
        assert!(client.is_authorized("worker2"));

        // Both should be authorized (using same connection flag)
        assert!(client.is_authorized("worker1"));
        assert!(client.is_authorized("worker2"));
    }

    #[test]
    fn test_authorization_workflow() {
        use sv1_api::methods::client_to_server::Authorize;

        // Create a DownstreamClient
        let mut client = DownstreamClient::default();

        // Initially not authorized
        assert!(!client.is_authorized("worker1"));

        // Handle authorize request (returns true but doesn't set flag in trait method)
        let auth_request = Authorize {
            id: 1,
            name: "worker1".to_string(),
            password: "password".to_string(),
        };
        let result = client.handle_authorize(&auth_request);
        assert!(result);

        // Manually authorize (simulating what the server would do after handle_authorize returns true)
        client.authorize("worker1");

        // Now should be authorized
        assert!(client.is_authorized("worker1"));
    }

    // ------------------------------------------------------------------------
    // handle_submit Tests
    // ------------------------------------------------------------------------

    #[test]
    fn test_handle_submit_returns_true() {
        // Create a DownstreamClient
        let client = DownstreamClient::default();

        // Create a minimal Submit request
        let submit_request = client_to_server::Submit {
            user_name: "worker1".to_string(),
            job_id: "1".to_string(),
            extra_nonce2: Sv1Extranonce::try_from(vec![0x00, 0x00, 0x00, 0x00])
                .expect("Valid extranonce2"),
            time: HexU32Be(0x6436eddf),
            nonce: HexU32Be(0x41d5deb0),
            version_bits: None,
            id: 1,
        };

        // Handle the submit
        let result = client.handle_submit(&submit_request);

        // Should return true (accepting the submission)
        assert!(result);
    }

    #[test]
    fn test_handle_submit_with_version_bits() {
        // Create a DownstreamClient
        let client = DownstreamClient::default();

        // Create a Submit request with version bits (version rolling)
        let submit_request = client_to_server::Submit {
            user_name: "worker1".to_string(),
            job_id: "2".to_string(),
            extra_nonce2: Sv1Extranonce::try_from(vec![0xaa, 0xbb, 0xcc, 0xdd])
                .expect("Valid extranonce2"),
            time: HexU32Be(0x6436eddf),
            nonce: HexU32Be(0x12345678),
            version_bits: Some(HexU32Be(0x20000000)),
            id: 2,
        };

        // Handle the submit
        let result = client.handle_submit(&submit_request);

        // Should return true (accepting the submission)
        assert!(result);
    }

    #[test]
    fn test_handle_submit_accepts_different_job_ids() {
        // Create a DownstreamClient
        let client = DownstreamClient::default();

        // Test multiple different job IDs
        let job_ids = vec!["1", "42", "999", "abc123"];

        for job_id in job_ids {
            let submit_request = client_to_server::Submit {
                user_name: "worker1".to_string(),
                job_id: job_id.to_string(),
                extra_nonce2: Sv1Extranonce::try_from(vec![0x00, 0x00, 0x00, 0x00])
                    .expect("Valid extranonce2"),
                time: HexU32Be(0x6436eddf),
                nonce: HexU32Be(0x41d5deb0),
                version_bits: None,
                id: 1,
            };

            let result = client.handle_submit(&submit_request);
            assert!(result, "Should accept job_id: {}", job_id);
        }
    }

    #[test]
    fn test_handle_submit_with_different_extranonce2() {
        // Create a DownstreamClient
        let client = DownstreamClient::default();

        // Test different extranonce2 values
        let extranonce2_values = vec![
            vec![0x00, 0x00, 0x00, 0x00],
            vec![0xff, 0xff, 0xff, 0xff],
            vec![0x12, 0x34, 0x56, 0x78],
            vec![0xaa, 0xbb, 0xcc, 0xdd],
        ];

        for (i, en2_bytes) in extranonce2_values.iter().enumerate() {
            let submit_request = client_to_server::Submit {
                user_name: "worker1".to_string(),
                job_id: "1".to_string(),
                extra_nonce2: Sv1Extranonce::try_from(en2_bytes.clone())
                    .expect("Valid extranonce2"),
                time: HexU32Be(0x6436eddf),
                nonce: HexU32Be(0x41d5deb0),
                version_bits: None,
                id: i as u64,
            };

            let result = client.handle_submit(&submit_request);
            assert!(result, "Should accept extranonce2: {:?}", en2_bytes);
        }
    }
}
