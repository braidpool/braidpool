//! Bitcoin integration tests for Braidpool
//!
//! These tests spin up a real Bitcoin Core node in regtest mode
//! to verify RPC connectivity and basic functionality.
//!
//! Requirements addressed (Issue #189):
//! - Spin up a regtest Bitcoin node for testing
//! - Test cookie authentication
//! - Test rpcauth (username/password) authentication
//! - Make basic RPC calls like getblockchaininfo

mod common;

use bitcoincore_rpc::{Auth, Client, RpcApi};
use common::BitcoinTestHarness;

/// Test that we can start a regtest node and connect via cookie auth
#[test]
fn test_regtest_node_startup() {
    let harness = BitcoinTestHarness::new_regtest().expect("Failed to start bitcoind");

    assert!(harness.is_running(), "bitcoind should be running");

    let info = harness
        .client()
        .get_blockchain_info()
        .expect("getblockchaininfo should succeed");

    assert_eq!(info.chain.to_string(), "regtest");
    assert_eq!(info.blocks, 0, "Fresh regtest should have 0 blocks");
}

/// Test cookie authentication (Issue #189 requirement)
#[test]
fn test_cookie_authentication() {
    let harness = BitcoinTestHarness::new_regtest().expect("Failed to start bitcoind");

    // Verify cookie file exists and is readable
    let cookie_path = harness.cookie_path();
    assert!(cookie_path.exists(), "Cookie file should exist");

    // Create a new client using only cookie auth
    let client = Client::new(
        harness.rpc_url().as_str(),
        Auth::CookieFile(cookie_path.clone()),
    )
    .expect("Cookie auth client creation should succeed");

    // Verify authentication works
    let result = client.get_network_info();
    assert!(result.is_ok(), "Cookie authenticated call should succeed");
}

/// Test UserPass (username/password) authentication (Issue #189 requirement)
///
/// This test verifies that the UserPass authentication mechanism works.
/// Bitcoin Core's cookie authentication uses a username:password format internally,
/// so we extract the cookie credentials and use them via UserPass auth.
#[test]
fn test_rpcauth_authentication() {
    // Start a node and use UserPass auth with credentials from the cookie file
    let harness = BitcoinTestHarness::new_regtest_with_auth("testuser", "testpassword123")
        .expect("Failed to start bitcoind with UserPass auth");

    // The harness is already using UserPass auth internally
    // Verify that RPC calls work
    let result = harness.client().get_blockchain_info();
    assert!(result.is_ok(), "UserPass authenticated call should succeed");

    let info = result.unwrap();
    assert_eq!(info.chain.to_string(), "regtest");
}

/// Test basic RPC calls - getblockchaininfo (Issue #189 requirement)
#[test]
fn test_getblockchaininfo() {
    let harness = BitcoinTestHarness::new_regtest().expect("Failed to start bitcoind");

    let info = harness
        .client()
        .get_blockchain_info()
        .expect("getblockchaininfo should succeed");

    // Verify expected fields
    assert_eq!(info.chain.to_string(), "regtest");
    assert!(info.verification_progress >= 0.0);
    assert!(info.verification_progress <= 1.0);
    // Note: initial_block_download may be true for fresh regtest with 0 blocks
}

/// Test getnetworkinfo RPC
#[test]
fn test_getnetworkinfo() {
    let harness = BitcoinTestHarness::new_regtest().expect("Failed to start bitcoind");

    let info = harness
        .client()
        .get_network_info()
        .expect("getnetworkinfo should succeed");

    assert!(info.version > 0);
    assert!(!info.subversion.is_empty());
}

/// Test block generation in regtest
#[test]
fn test_generate_blocks() {
    let harness = BitcoinTestHarness::new_regtest().expect("Failed to start bitcoind");

    // Generate 101 blocks (100 for coinbase maturity + 1)
    let block_hashes = harness
        .generate_blocks(101)
        .expect("generate_blocks should succeed");

    assert_eq!(block_hashes.len(), 101);

    // Verify blockchain height
    let info = harness
        .client()
        .get_blockchain_info()
        .expect("getblockchaininfo should succeed");
    assert_eq!(info.blocks, 101);
}

/// Test getblock and getblockhash RPC
#[test]
fn test_block_retrieval() {
    let harness = BitcoinTestHarness::new_regtest().expect("Failed to start bitcoind");

    // Generate a block first
    let hashes = harness
        .generate_blocks(1)
        .expect("generate_blocks should succeed");

    // Get block by hash
    let block_hash = hashes[0];
    let block = harness
        .client()
        .get_block(&block_hash)
        .expect("getblock should succeed");

    assert_eq!(block.header.block_hash(), block_hash);

    // Get block hash by height
    let hash_at_1 = harness
        .client()
        .get_block_hash(1)
        .expect("getblockhash should succeed");

    assert_eq!(hash_at_1, block_hash);
}

/// Test getblocktemplate RPC (critical for mining)
#[test]
fn test_getblocktemplate() {
    let harness = BitcoinTestHarness::new_regtest().expect("Failed to start bitcoind");

    // Generate some blocks first to have a mature coinbase
    harness
        .generate_blocks(101)
        .expect("generate_blocks should succeed");

    // Get block template - must pass segwit rule for modern Bitcoin Core
    use bitcoincore_rpc::json::{GetBlockTemplateModes, GetBlockTemplateRules};
    let template = harness
        .client()
        .get_block_template(
            GetBlockTemplateModes::Template,
            &[GetBlockTemplateRules::SegWit],
            &[],
        )
        .expect("getblocktemplate should succeed");

    assert!(template.height > 0);
    assert!(!template.bits.is_empty());
}

/// Test mempool operations
#[test]
fn test_mempool_operations() {
    let harness = BitcoinTestHarness::new_regtest().expect("Failed to start bitcoind");

    // Initially mempool should be empty
    let mempool = harness
        .client()
        .get_raw_mempool()
        .expect("getrawmempool should succeed");

    assert!(mempool.is_empty(), "Fresh regtest mempool should be empty");

    let info = harness
        .client()
        .get_mempool_info()
        .expect("getmempoolinfo should succeed");

    assert_eq!(info.size, 0);
}

/// Test connection error handling
#[test]
fn test_connection_error_handling() {
    // Try to connect to a non-existent node
    let result = Client::new(
        "http://127.0.0.1:59999", // Very unlikely to be in use
        Auth::None,
    );

    // Client creation succeeds, but RPC calls should fail
    if let Ok(client) = result {
        let rpc_result = client.get_blockchain_info();
        assert!(
            rpc_result.is_err(),
            "Connection to non-existent node should fail"
        );
    }
}
