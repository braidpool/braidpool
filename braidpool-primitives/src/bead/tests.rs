use bitcoin::absolute::Time;
use bitcoin::ecdsa::Signature;
use bitcoin::secp256k1::PublicKey;
use bitcoin::{Address, BlockHash, BlockHeader, BlockTime, BlockVersion, CompactTarget, Network,
              TxMerkleNode};
use core::net::SocketAddr;
use secp256k1::{Secp256k1, SecretKey};
use std::net::{IpAddr, Ipv4Addr};
use std::str::FromStr;

use super::{canonicalize_parents, Bead, CanonicalizeError, CommittedMetadata, UnCommittedMetadata};

fn test_address() -> Address {
    Address::from_str("32iVBEu4dxkUQk9dJbZUiBiQdmypcEyJRf")
        .unwrap()
        .require_network(Network::Bitcoin)
        .unwrap()
}

fn test_pubkey() -> PublicKey {
    let secp = Secp256k1::new();
    let secret_key = SecretKey::from_byte_array(&[0xcd; 32]).expect("32 bytes, within curve order");
    PublicKey::from_secret_key(&secp, &secret_key)
}

fn test_socket() -> SocketAddr {
    SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080)
}

#[test]
fn test_serialized_bead() {
    let committed = CommittedMetadata {
        transaction_cnt: 0,
        parents: Vec::new(),
        transactions: vec![],
        payout_address: test_address(),
        comm_pub_key: test_pubkey(),
        observed_time_at_node: Time::from_consensus(1653195600).unwrap(),
        miner_ip: test_socket(),
    };

    let hex = "3046022100839c1fbc5304de944f697c9f4b1d01d1faeba32d751c0f7acb21ac8a0f436a72022100e89bd46bb3a5a62adc679f659b7ce876d83ee297c7a5587b2011c4fcc72eab45";
    let sig = Signature {
        signature: secp256k1::ecdsa::Signature::from_str(hex).unwrap(),
        sighash_type: bitcoin::EcdsaSighashType::All,
    };

    let uncommitted = UnCommittedMetadata {
        extra_nonce: 12,
        broadcast_timestamp: Time::from_consensus(1653195600).unwrap(),
        signature: sig,
        parent_bead_timestamps: Vec::new(),
    };

    let test_bytes = [0u8; 32];
    let test_bead = Bead {
        block_header: BlockHeader {
            version: BlockVersion::TWO,
            prev_blockhash: BlockHash::from_byte_array(test_bytes),
            bits: CompactTarget::from_consensus(32),
            nonce: 1,
            time: BlockTime::from_u32(8328429),
            merkle_root: TxMerkleNode::from_byte_array(test_bytes),
        },
        committed_metadata: committed,
        uncommitted_metadata: uncommitted,
    };

    let serialized_str = serde_json::to_string(&test_bead).unwrap();
    assert_eq!(
        serialized_str,
        r#"{"block_header":{"version":2,"prev_blockhash":"0000000000000000000000000000000000000000000000000000000000000000","merkle_root":"0000000000000000000000000000000000000000000000000000000000000000","time":8328429,"bits":32,"nonce":1},"committed_metadata":{"transaction_cnt":0,"transactions":[],"parents":[],"payout_address":"32iVBEu4dxkUQk9dJbZUiBiQdmypcEyJRf","observed_time_at_node":1653195600,"comm_pub_key":"02b98a7fb8cc007048625b6446ad49a1b3a722df8c1ca975b87160023e14d19097","miner_ip":"127.0.0.1:8080"},"uncommitted_metadata":{"extra_nonce":12,"broadcast_timestamp":1653195600,"signature":{"signature":"3046022100839c1fbc5304de944f697c9f4b1d01d1faeba32d751c0f7acb21ac8a0f436a72022100e89bd46bb3a5a62adc679f659b7ce876d83ee297c7a5587b2011c4fcc72eab45","sighash_type":"SIGHASH_ALL"},"parent_bead_timestamps":[]}}"#
    );
}

#[test]
fn test_committed_metadata_new_enforces_ordering() {
    let parents = vec![
        (BlockHash::from_byte_array([3u8; 32]), Time::from_consensus(1700000003).unwrap()),
        (BlockHash::from_byte_array([1u8; 32]), Time::from_consensus(1700000001).unwrap()),
        (BlockHash::from_byte_array([2u8; 32]), Time::from_consensus(1700000002).unwrap()),
    ];

    let committed = CommittedMetadata::new(
        0,
        vec![],
        parents,
        test_address(),
        Time::from_consensus(1653195600).unwrap(),
        test_pubkey(),
        test_socket(),
    );

    // Parents must be sorted ascending by hash
    assert_eq!(committed.parents[0], BlockHash::from_byte_array([1u8; 32]));
    assert_eq!(committed.parents[1], BlockHash::from_byte_array([2u8; 32]));
    assert_eq!(committed.parents[2], BlockHash::from_byte_array([3u8; 32]));
}

#[test]
fn test_canonicalize_parents_deterministic_serialization() {
    let mut parents = vec![
        BlockHash::from_byte_array([3u8; 32]),
        BlockHash::from_byte_array([1u8; 32]),
        BlockHash::from_byte_array([2u8; 32]),
    ];
    let mut timestamps = vec![
        Time::from_consensus(1700000100).unwrap(),
        Time::from_consensus(1700000200).unwrap(),
        Time::from_consensus(1700000300).unwrap(),
    ];

    canonicalize_parents(&mut parents, &mut timestamps).unwrap();

    let committed = CommittedMetadata {
        transaction_cnt: 0,
        parents,
        transactions: vec![],
        payout_address: test_address(),
        comm_pub_key: test_pubkey(),
        observed_time_at_node: Time::from_consensus(1653195600).unwrap(),
        miner_ip: test_socket(),
    };

    // Serialize 5 times and assert identical output each time
    let serialized = serde_json::to_string(&committed).unwrap();
    for _ in 0..4 {
        assert_eq!(serde_json::to_string(&committed).unwrap(), serialized);
    }
}

#[test]
fn test_canonicalize_parents_integration() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    // Build the same parents in 3 different insertion orders
    let parent_sets = vec![
        vec![
            (BlockHash::from_byte_array([3u8; 32]), Time::from_consensus(1700000003).unwrap()),
            (BlockHash::from_byte_array([1u8; 32]), Time::from_consensus(1700000001).unwrap()),
            (BlockHash::from_byte_array([2u8; 32]), Time::from_consensus(1700000002).unwrap()),
        ],
        vec![
            (BlockHash::from_byte_array([1u8; 32]), Time::from_consensus(1700000001).unwrap()),
            (BlockHash::from_byte_array([2u8; 32]), Time::from_consensus(1700000002).unwrap()),
            (BlockHash::from_byte_array([3u8; 32]), Time::from_consensus(1700000003).unwrap()),
        ],
        vec![
            (BlockHash::from_byte_array([2u8; 32]), Time::from_consensus(1700000002).unwrap()),
            (BlockHash::from_byte_array([3u8; 32]), Time::from_consensus(1700000003).unwrap()),
            (BlockHash::from_byte_array([1u8; 32]), Time::from_consensus(1700000001).unwrap()),
        ],
    ];

    let mut hashes = Vec::new();
    for ps in &parent_sets {
        let committed = CommittedMetadata::new(
            0, vec![], ps.clone(),
            test_address(),
            Time::from_consensus(1653195600).unwrap(),
            test_pubkey(), test_socket(),
        );
        let bytes = serde_json::to_string(&committed).unwrap();
        let mut h = DefaultHasher::new();
        bytes.hash(&mut h);
        hashes.push(h.finish());
    }

    // All three insertion orders must produce the same hash
    assert_eq!(hashes[0], hashes[1]);
    assert_eq!(hashes[1], hashes[2]);
}

#[test]
fn test_canonicalize_parents_orders_by_hash() {
    let mut parents = vec![
        BlockHash::from_byte_array([3u8; 32]),
        BlockHash::from_byte_array([1u8; 32]),
        BlockHash::from_byte_array([2u8; 32]),
    ];
    let mut timestamps = vec![
        Time::from_consensus(1700000300).unwrap(),
        Time::from_consensus(1700000100).unwrap(),
        Time::from_consensus(1700000200).unwrap(),
    ];

    canonicalize_parents(&mut parents, &mut timestamps).unwrap();

    assert_eq!(parents[0], BlockHash::from_byte_array([1u8; 32]));
    assert_eq!(parents[1], BlockHash::from_byte_array([2u8; 32]));
    assert_eq!(parents[2], BlockHash::from_byte_array([3u8; 32]));

    assert_eq!(timestamps[0], Time::from_consensus(1700000100).unwrap());
    assert_eq!(timestamps[1], Time::from_consensus(1700000200).unwrap());
    assert_eq!(timestamps[2], Time::from_consensus(1700000300).unwrap());
}

#[test]
fn test_canonicalize_parents_returns_error_on_mismatched_lengths() {
    let mut parents = vec![BlockHash::from_byte_array([1u8; 32])];
    let mut timestamps = Vec::new();

    let result = canonicalize_parents(&mut parents, &mut timestamps);
    assert_eq!(result, Err(CanonicalizeError { parents_len: 1, timestamps_len: 0 }));
}

#[test]
fn test_canonicalize_parents_empty() {
    let mut parents: Vec<BlockHash> = Vec::new();
    let mut timestamps: Vec<Time> = Vec::new();

    canonicalize_parents(&mut parents, &mut timestamps).unwrap();

    assert!(parents.is_empty());
    assert!(timestamps.is_empty());
}

#[test]
fn test_canonicalize_parents_single() {
    let hash = BlockHash::from_byte_array([42u8; 32]);
    let time = Time::from_consensus(1700000999).unwrap();

    let mut parents = vec![hash];
    let mut timestamps = vec![time];

    canonicalize_parents(&mut parents, &mut timestamps).unwrap();

    assert_eq!(parents.len(), 1);
    assert_eq!(parents[0], hash);
    assert_eq!(timestamps[0], time);
}
