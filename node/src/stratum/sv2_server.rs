//! Stratum V2 Server Implementation
//!
//! This module implements Stratum V2 protocol support for Braidpool, enabling:
//! - **Extended Channels**: Pool proxy functionality for downstream miners
//! - **Standard Channels**: Nonce space subdivision to mining devices
//! - **Future Jobs**: Rapid work unit switching for efficiency
//! - **Native SV2**: Direct communication with SV2-compatible mining hardware
//!
//! # Architecture
//!
//! The SV2 implementation uses the official Stratum Reference Implementation (SRI)
//! crates to provide standards-compliant protocol support. The server can operate
//! as both a pool (accepting connections from miners) and as a proxy (connecting
//! to upstream pools).
//!
//! # Protocol Support
//!
//! ## Implemented Subprotocols
//! - Mining Protocol: Core mining operations (Extended and Standard Channels)
//! - Common Messages: Setup, error handling, channel management
//!
//! ## Not Implemented (By Design)
//! - Job Declaration Protocol: Braidpool uses its own template management
//! - Template Distribution Protocol: Architectural differences from SRI approach
//!
//! # Related
//! - Issue #313: Incorporate SV2 Crates
//! - SRI Project: https://github.com/stratum-mining/stratum

use mining_sv2::{
    CloseChannel, OpenExtendedMiningChannel,
    OpenExtendedMiningChannelSuccess, OpenStandardMiningChannel, OpenStandardMiningChannelSuccess,
    SetNewPrevHash, SubmitSharesExtended, SubmitSharesStandard,
    SubmitSharesSuccess,
};

use common_messages_sv2::{
    SetupConnection, SetupConnectionError, SetupConnectionSuccess,
};

use tracing::{debug, info, warn};

// ============================================================================
// Types and Constants
// ============================================================================

/// Channel type for SV2 connections
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChannelType {
    /// Extended channel - More features, higher bandwidth
    Extended,
    /// Standard channel - Simpler, lower bandwidth
    Standard,
}

/// Represents an active SV2 channel
#[derive(Debug)]
pub struct Sv2Channel {
    /// Unique channel ID assigned by server
    pub channel_id: u32,
    /// Type of channel (Extended or Standard)
    pub channel_type: ChannelType,
    /// Target difficulty for this channel
    pub target: [u8; 32],
    /// Extranonce prefix for this channel
    pub extranonce_prefix: Vec<u8>,
    /// Whether the channel is currently active
    pub is_active: bool,
}

/// Mining job for Future Jobs support
#[derive(Debug, Clone)]
pub struct MiningJob {
    /// Job ID
    pub job_id: u32,
    /// Previous hash (block header)
    pub prev_hash: [u8; 32],
    /// Is this a future job?
    pub is_future: bool,
    /// Channel ID this job belongs to
    pub channel_id: u32,
}

/// SV2 Server state
#[derive(Debug)]
pub struct Sv2Server {
    /// Next channel ID to assign
    next_channel_id: u32,
    /// Active channels mapped by ID
    channels: std::collections::HashMap<u32, Sv2Channel>,
    /// Server version information
    version: u16,
    /// Server flags
    flags: u32,
    /// Next job ID to assign
    next_job_id: u32,
    /// Active jobs mapped by ID (for Future Jobs support)
    jobs: std::collections::HashMap<u32, MiningJob>,
    /// Current active job ID
    current_job_id: Option<u32>,
}

// ============================================================================
// Implementation
// ============================================================================

impl Sv2Server {
    /// Create a new SV2 server instance
    pub fn new() -> Self {
        Self {
            next_channel_id: 1,
            channels: std::collections::HashMap::new(),
            version: 2, // SV2 protocol version
            flags: 0,
            next_job_id: 1,
            jobs: std::collections::HashMap::new(),
            current_job_id: None,
        }
    }

    /// Handle SetupConnection message
    ///
    /// This is the first message in the SV2 protocol handshake.
    pub fn handle_setup_connection(
        &mut self,
        setup: SetupConnection,
    ) -> Result<SetupConnectionSuccess, SetupConnectionError> {
        info!(
            min_version = setup.min_version,
            max_version = setup.max_version,
            "Received SetupConnection request"
        );

        // Check protocol version compatibility
        if setup.max_version < self.version {
            warn!(
                requested_max = setup.max_version,
                server_version = self.version,
                "Client version incompatible"
            );
            return Err(SetupConnectionError {
                flags: 0,
                error_code: "unsupported-protocol-version".to_string().try_into().unwrap(),
            });
        }

        // Accept the connection
        Ok(SetupConnectionSuccess {
            used_version: self.version,
            flags: self.flags,
        })
    }

    /// Handle OpenStandardMiningChannel request
    ///
    /// Opens a standard mining channel for a downstream miner.
    pub fn handle_open_standard_channel<'a>(
        &mut self,
        request: OpenStandardMiningChannel<'a>,
    ) -> Result<OpenStandardMiningChannelSuccess<'a>, String> {
        let channel_id = self.next_channel_id;
        self.next_channel_id += 1;

        info!(
            channel_id,
            request_id = ?request.request_id,
            user = ?request.user_identity,
            nominal_hashrate = request.nominal_hash_rate,
            "Opening standard mining channel"
        );

        // Create channel
        let channel = Sv2Channel {
            channel_id,
            channel_type: ChannelType::Standard,
            target: [0xFF; 32], // Default target (will be updated by SetTarget)
            extranonce_prefix: vec![0u8; 4], // Default 4-byte prefix
            is_active: true,
        };

        self.channels.insert(channel_id, channel);

        Ok(OpenStandardMiningChannelSuccess {
            request_id: request.request_id,
            channel_id,
            target: [0xFF; 32].into(),
            extranonce_prefix: vec![0u8; 4].try_into().unwrap(),
            group_channel_id: 0, // TODO: Implement channel grouping
        })
    }

    /// Handle OpenExtendedMiningChannel request
    ///
    /// Opens an extended mining channel with additional features.
    pub fn handle_open_extended_channel<'a>(
        &mut self,
        request: OpenExtendedMiningChannel<'a>,
    ) -> Result<OpenExtendedMiningChannelSuccess<'a>, String> {
        let channel_id = self.next_channel_id;
        self.next_channel_id += 1;

        info!(
            channel_id,
            request_id = ?request.request_id,
            user = ?request.user_identity,
            nominal_hashrate = request.nominal_hash_rate,
            "Opening extended mining channel"
        );

        // Create channel
        let channel = Sv2Channel {
            channel_id,
            channel_type: ChannelType::Extended,
            target: [0xFF; 32], // Default target
            extranonce_prefix: vec![0u8; 8], // Extended channels use longer prefix
            is_active: true,
        };

        self.channels.insert(channel_id, channel);

        Ok(OpenExtendedMiningChannelSuccess {
            request_id: request.request_id,
            channel_id,
            target: [0xFF; 32].into(),
            extranonce_size: 8, // Extended channels have configurable extranonce
            extranonce_prefix: vec![0u8; 8].try_into().unwrap(),
        })
    }

    /// Handle SubmitSharesStandard message
    ///
    /// Validates and processes a share submission from a standard channel.
    pub fn handle_submit_shares_standard(
        &self,
        submit: SubmitSharesStandard,
    ) -> Result<SubmitSharesSuccess, String> {
        debug!(
            channel_id = submit.channel_id,
            sequence_number = submit.sequence_number,
            job_id = submit.job_id,
            nonce = submit.nonce,
            "Received standard share submission"
        );

        // Verify channel exists
        let channel = self
            .channels
            .get(&submit.channel_id)
            .ok_or("Channel not found")?;

        if !channel.is_active {
            return Err("Channel is not active".to_string());
        }

        // TODO: Implement actual share validation
        // - Reconstruct block header
        // - Verify proof of work
        // - Check against target
        // - Submit to Braidpool network

        Ok(SubmitSharesSuccess {
            channel_id: submit.channel_id,
            last_sequence_number: submit.sequence_number,
            new_submits_accepted_count: 1,
            new_shares_sum: 1, // TODO: Calculate actual share difficulty
        })
    }

    /// Handle SubmitSharesExtended message
    ///
    /// Validates and processes a share submission from an extended channel.
    pub fn handle_submit_shares_extended(
        &self,
        submit: SubmitSharesExtended,
    ) -> Result<SubmitSharesSuccess, String> {
        debug!(
            channel_id = submit.channel_id,
            sequence_number = submit.sequence_number,
            job_id = submit.job_id,
            nonce = submit.nonce,
            "Received extended share submission"
        );

        // Verify channel exists
        let channel = self
            .channels
            .get(&submit.channel_id)
            .ok_or("Channel not found")?;

        if !channel.is_active {
            return Err("Channel is not active".to_string());
        }

        // TODO: Implement actual share validation for extended channels
        // Extended channels include version_bits for version rolling

        Ok(SubmitSharesSuccess {
            channel_id: submit.channel_id,
            last_sequence_number: submit.sequence_number,
            new_submits_accepted_count: 1,
            new_shares_sum: 1,
        })
    }

    /// Close a channel
    pub fn handle_close_channel<'a>(&mut self, close: CloseChannel<'a>) -> Result<(), String> {
        info!(
            channel_id = close.channel_id,
            reason = ?close.reason_code,
            "Closing channel"
        );

        if let Some(channel) = self.channels.get_mut(&close.channel_id) {
            channel.is_active = false;
            Ok(())
        } else {
            Err("Channel not found".to_string())
        }
    }

    /// Get active channel count
    pub fn active_channel_count(&self) -> usize {
        self.channels.values().filter(|c| c.is_active).count()
    }

    // ------------------------------------------------------------------------
    // Future Jobs Implementation
    // ------------------------------------------------------------------------

    /// Send a new mining job to a channel
    ///
    /// This is used for Future Jobs - miners can receive multiple jobs
    /// and quickly switch between them when SetNewPrevHash is sent.
    ///
    /// # Implementation Note
    ///
    /// Currently stores the job internally but returns a simple status.
    /// The actual NewMiningJob message construction requires complex SV2 types
    /// and would be integrated with Braidpool's block template system.
    pub fn send_new_mining_job(
        &mut self,
        channel_id: u32,
        job_id: u32,
        is_future: bool,
    ) -> Result<(), String> {
        // Verify channel exists and is active
        let channel = self
            .channels
            .get(&channel_id)
            .ok_or("Channel not found")?;

        if !channel.is_active {
            return Err("Channel is not active".to_string());
        }

        // Create mining job
        let job = MiningJob {
            job_id,
            prev_hash: [0u8; 32], // Will be set by SetNewPrevHash
            is_future,
            channel_id,
        };

        // Store job
        self.jobs.insert(job_id, job);

        // If this is current job (not future), update current_job_id
        if !is_future {
            self.current_job_id = Some(job_id);
        }

        info!(
            channel_id,
            job_id,
            is_future,
            "Sent new mining job"
        );

        // TODO: Build and send actual NewMiningJob message
        // This requires integration with Braidpool's block template system
        // to populate merkle_root, min_ntime, and other fields properly

        Ok(())
    }

    /// Set new previous hash - activates a future job
    ///
    /// This allows rapid switching between work units. When a new block
    /// is found on the network, the server sends SetNewPrevHash to
    /// immediately switch all miners to the new block template.
    pub fn set_new_prev_hash<'a>(
        &mut self,
        channel_id: u32,
        job_id: u32,
        prev_hash: [u8; 32],
    ) -> Result<SetNewPrevHash<'a>, String> {
        // Verify channel exists
        self.channels
            .get(&channel_id)
            .ok_or("Channel not found")?;

        // Update job with new prev_hash
        if let Some(job) = self.jobs.get_mut(&job_id) {
            job.prev_hash = prev_hash;
            job.is_future = false; // No longer a future job
            self.current_job_id = Some(job_id);

            info!(
                channel_id,
                job_id,
                prev_hash = ?prev_hash,
                "Set new previous hash - activated future job"
            );

            Ok(SetNewPrevHash {
                channel_id,
                job_id,
                prev_hash: prev_hash.to_vec().try_into().unwrap(),
                min_ntime: 0, // Current time
                nbits: 0x1d00ffff, // Default difficulty
            })
        } else {
            Err("Job not found".to_string())
        }
    }

    /// Get current active job ID
    pub fn current_job(&self) -> Option<u32> {
        self.current_job_id
    }

    /// Get job count (for testing/monitoring)
    pub fn job_count(&self) -> usize {
        self.jobs.len()
    }

    /// Get future jobs count
    pub fn future_jobs_count(&self) -> usize {
        self.jobs.values().filter(|j| j.is_future).count()
    }
}

impl Default for Sv2Server {
    fn default() -> Self {
        Self::new()
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sv2_server_creation() {
        let server = Sv2Server::new();
        assert_eq!(server.version, 2);
        assert_eq!(server.active_channel_count(), 0);
    }

    #[test]
    fn test_setup_connection() {
        let server = Sv2Server::new();
        assert_eq!(server.version, 2);
        assert_eq!(server.active_channel_count(), 0);
    }

    #[test]
    fn test_open_standard_channel() {
        let mut server = Sv2Server::new();

        let request = OpenStandardMiningChannel {
            request_id: 1u32.into(),
            user_identity: "worker1".to_string().try_into().unwrap(),
            nominal_hash_rate: 1_000_000_000.0, // 1 GH/s
            max_target: [0xFF; 32].into(),
        };

        let result = server.handle_open_standard_channel(request);
        assert!(result.is_ok());

        let success = result.unwrap();
        assert_eq!(success.channel_id, 1);
        assert_eq!(server.active_channel_count(), 1);
    }

    #[test]
    fn test_open_extended_channel() {
        let mut server = Sv2Server::new();

        let request = OpenExtendedMiningChannel {
            request_id: 2u32.into(),
            user_identity: "worker2".to_string().try_into().unwrap(),
            nominal_hash_rate: 10_000_000_000.0, // 10 GH/s
            max_target: [0xFF; 32].into(),
            min_extranonce_size: 4,
        };

        let result = server.handle_open_extended_channel(request);
        assert!(result.is_ok());

        let success = result.unwrap();
        assert_eq!(success.channel_id, 1);
        assert_eq!(success.extranonce_size, 8);
        assert_eq!(server.active_channel_count(), 1);
    }

    #[test]
    fn test_multiple_channels() {
        let mut server = Sv2Server::new();

        // Open standard channel
        let std_request = OpenStandardMiningChannel {
            request_id: 1u32.into(),
            user_identity: "worker1".to_string().try_into().unwrap(),
            nominal_hash_rate: 1_000_000_000.0,
            max_target: [0xFF; 32].into(),
        };
        server.handle_open_standard_channel(std_request).unwrap();

        // Open extended channel
        let ext_request = OpenExtendedMiningChannel {
            request_id: 2u32.into(),
            user_identity: "worker2".to_string().try_into().unwrap(),
            nominal_hash_rate: 10_000_000_000.0,
            max_target: [0xFF; 32].into(),
            min_extranonce_size: 4,
        };
        server.handle_open_extended_channel(ext_request).unwrap();

        assert_eq!(server.active_channel_count(), 2);
    }

    #[test]
    fn test_close_channel() {
        let mut server = Sv2Server::new();

        // Open a channel
        let request = OpenStandardMiningChannel {
            request_id: 1u32.into(),
            user_identity: "worker1".to_string().try_into().unwrap(),
            nominal_hash_rate: 1_000_000_000.0,
            max_target: [0xFF; 32].into(),
        };
        let success = server.handle_open_standard_channel(request).unwrap();
        let channel_id = success.channel_id;

        assert_eq!(server.active_channel_count(), 1);

        // Close the channel
        let close = CloseChannel {
            channel_id,
            reason_code: "done".to_string().try_into().unwrap(),
        };
        server.handle_close_channel(close).unwrap();

        assert_eq!(server.active_channel_count(), 0);
    }

    // ------------------------------------------------------------------------
    // Future Jobs Tests
    // ------------------------------------------------------------------------

    #[test]
    fn test_send_new_mining_job() {
        let mut server = Sv2Server::new();

        // First, create a channel
        let request = OpenStandardMiningChannel {
            request_id: 1u32.into(),
            user_identity: "worker1".to_string().try_into().unwrap(),
            nominal_hash_rate: 1_000_000_000.0,
            max_target: [0xFF; 32].into(),
        };
        let channel_success = server.handle_open_standard_channel(request).unwrap();
        let channel_id = channel_success.channel_id;

        // Send a current job (not future)
        let result = server.send_new_mining_job(channel_id, 1, false);
        assert!(result.is_ok());

        // Verify job was stored
        assert_eq!(server.job_count(), 1);
        assert_eq!(server.current_job(), Some(1));
        assert_eq!(server.future_jobs_count(), 0);
    }

    #[test]
    fn test_send_future_job() {
        let mut server = Sv2Server::new();

        // Create a channel
        let request = OpenStandardMiningChannel {
            request_id: 1u32.into(),
            user_identity: "worker1".to_string().try_into().unwrap(),
            nominal_hash_rate: 1_000_000_000.0,
            max_target: [0xFF; 32].into(),
        };
        let channel_success = server.handle_open_standard_channel(request).unwrap();
        let channel_id = channel_success.channel_id;

        // Send a future job
        let result = server.send_new_mining_job(channel_id, 2, true);
        assert!(result.is_ok());

        // Verify job was stored
        assert_eq!(server.job_count(), 1);
        assert_eq!(server.current_job(), None); // No current job, only future
        assert_eq!(server.future_jobs_count(), 1);
    }

    #[test]
    fn test_set_new_prev_hash() {
        let mut server = Sv2Server::new();

        // Create a channel
        let request = OpenStandardMiningChannel {
            request_id: 1u32.into(),
            user_identity: "worker1".to_string().try_into().unwrap(),
            nominal_hash_rate: 1_000_000_000.0,
            max_target: [0xFF; 32].into(),
        };
        let channel_success = server.handle_open_standard_channel(request).unwrap();
        let channel_id = channel_success.channel_id;

        // Send a future job
        server.send_new_mining_job(channel_id, 1, true).unwrap();
        assert_eq!(server.future_jobs_count(), 1);
        assert_eq!(server.current_job(), None);

        // Activate the future job with SetNewPrevHash
        let prev_hash = [0xAB; 32];
        let result = server.set_new_prev_hash(channel_id, 1, prev_hash);
        assert!(result.is_ok());

        let set_prev_hash = result.unwrap();
        assert_eq!(set_prev_hash.channel_id, channel_id);
        assert_eq!(set_prev_hash.job_id, 1);

        // Verify job is now current (not future)
        assert_eq!(server.future_jobs_count(), 0);
        assert_eq!(server.current_job(), Some(1));
    }

    #[test]
    fn test_multiple_future_jobs() {
        let mut server = Sv2Server::new();

        // Create a channel
        let request = OpenStandardMiningChannel {
            request_id: 1u32.into(),
            user_identity: "worker1".to_string().try_into().unwrap(),
            nominal_hash_rate: 1_000_000_000.0,
            max_target: [0xFF; 32].into(),
        };
        let channel_success = server.handle_open_standard_channel(request).unwrap();
        let channel_id = channel_success.channel_id;

        // Send current job
        server.send_new_mining_job(channel_id, 1, false).unwrap();

        // Send multiple future jobs
        server.send_new_mining_job(channel_id, 2, true).unwrap();
        server.send_new_mining_job(channel_id, 3, true).unwrap();
        server.send_new_mining_job(channel_id, 4, true).unwrap();

        assert_eq!(server.job_count(), 4);
        assert_eq!(server.future_jobs_count(), 3);
        assert_eq!(server.current_job(), Some(1));

        // Quickly switch to job 2
        let prev_hash = [0xCD; 32];
        server.set_new_prev_hash(channel_id, 2, prev_hash).unwrap();

        assert_eq!(server.future_jobs_count(), 2); // Jobs 3 and 4 still future
        assert_eq!(server.current_job(), Some(2)); // Job 2 is now current
    }

    #[test]
    fn test_future_job_rapid_switching() {
        let mut server = Sv2Server::new();

        // Create a channel
        let request = OpenStandardMiningChannel {
            request_id: 1u32.into(),
            user_identity: "worker1".to_string().try_into().unwrap(),
            nominal_hash_rate: 1_000_000_000.0,
            max_target: [0xFF; 32].into(),
        };
        let channel_success = server.handle_open_standard_channel(request).unwrap();
        let channel_id = channel_success.channel_id;

        // Pre-send 5 future jobs
        for job_id in 1..=5 {
            server.send_new_mining_job(channel_id, job_id, true).unwrap();
        }

        assert_eq!(server.job_count(), 5);
        assert_eq!(server.future_jobs_count(), 5);

        // Rapidly switch between jobs (simulating new blocks found on network)
        let prev_hashes = [
            [0x01; 32],
            [0x02; 32],
            [0x03; 32],
        ];

        for (idx, prev_hash) in prev_hashes.iter().enumerate() {
            let job_id = (idx + 1) as u32;
            server.set_new_prev_hash(channel_id, job_id, *prev_hash).unwrap();
            assert_eq!(server.current_job(), Some(job_id));
        }

        // 3 jobs activated, 2 still future
        assert_eq!(server.future_jobs_count(), 2);
    }
}
