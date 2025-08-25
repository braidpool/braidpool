use super::Bead;
use super::BeadCodec;
use super::BeadHash;
use super::BeadRequest;
use super::BeadResponse;
use super::BeadSyncError;
use super::CommittedMetadata;
use super::UnCommittedMetadata;
use crate::committed_metadata::TimeVec;
use crate::utils::create_test_bead;
use crate::utils::test_utils::test_utility_functions::*;
use bitcoin::absolute::Time;
use bitcoin::consensus::encode::deserialize;
use bitcoin::consensus::encode::Decodable;
use bitcoin::consensus::encode::Encodable;
use bitcoin::consensus::serialize;
use bitcoin::consensus::DeserializeError;
use bitcoin::ecdsa::Signature;
use bitcoin::pow::CompactTargetExt;
use bitcoin::BlockHash;
use bitcoin::BlockHeader;
use bitcoin::BlockTime;
use bitcoin::BlockVersion;
use bitcoin::CompactTarget;
use bitcoin::EcdsaSighashType;
use bitcoin::TxMerkleNode;
use bitcoin::Txid;
use futures::executor::block_on;
use libp2p::request_response::Codec;
use std::collections::HashSet;
use std::io::Cursor;
use std::str::FromStr;
#[test]

fn test_serialized_committed_metadata() {
    let _address = String::from("127.0.0.1:8000");
    let public_key = "020202020202020202020202020202020202020202020202020202020202020202"
        .parse::<bitcoin::PublicKey>()
        .unwrap();
    let socket = String::from("127.0.0.1");
    let time_val = Time::from_consensus(1653195600).unwrap();
    let parent_hash_set: HashSet<BlockHash> = HashSet::new();
    let time_hash_set = TimeVec(Vec::new());
    let weak_target = CompactTarget::from_unprefixed_hex("1d00ffff").unwrap();
    let min_target = CompactTarget::from_unprefixed_hex("1d00ffff").unwrap();
    let test_committed_metadata = TestCommittedMetadataBuilder::new()
        .comm_pub_key(public_key)
        .miner_ip(socket)
        .start_timestamp(time_val)
        .parents(parent_hash_set)
        .parent_bead_timestamps(time_hash_set)
        .payout_address(_address)
        .transactions(vec![])
        .min_target(min_target)
        .weak_target(weak_target)
        .build();
    let serialized_val = serialize(&test_committed_metadata);
    let deserialized_result: Result<CommittedMetadata, DeserializeError> =
        deserialize(&serialized_val);
    let deserialized_test = match deserialized_result {
        Ok(val) => val,
        Err(error) => {
            panic!(
                "An error occurred while deserializaing committed metadata {:?}",
                error
            );
        }
    };
    assert_eq!(deserialized_test, test_committed_metadata);
}
#[test]

fn test_serialized_uncommitted_metadata() {
    let hex = "3046022100839c1fbc5304de944f697c9f4b1d01d1faeba32d751c0f7acb21ac8a0f436a72022100e89bd46bb3a5a62adc679f659b7ce876d83ee297c7a5587b2011c4fcc72eab45";
    let sig = Signature {
        signature: secp256k1::ecdsa::Signature::from_str(hex).unwrap(),
        sighash_type: EcdsaSighashType::All,
    };
    let time_val = Time::from_consensus(1653195600).unwrap();
    let extra_nonce = 42;
    let test_uncommitted_metadata = TestUnCommittedMetadataBuilder::new()
        .broadcast_timestamp(time_val)
        .extra_nonce(extra_nonce, extra_nonce)
        .signature(sig)
        .build();
    let serialized_val = serialize(&test_uncommitted_metadata);

    let deserialized_result: Result<UnCommittedMetadata, DeserializeError> =
        deserialize(&serialized_val);
    let deserialized_test = match deserialized_result {
        Ok(val) => val,
        Err(error) => {
            panic!(
                "An error occurred while deserializaing uncommitted metadata {:?}",
                error
            );
        }
    };
    assert_eq!(deserialized_test, test_uncommitted_metadata);
}
#[test]

fn test_serialized_bead() {
    let _address = String::from("127.0.0.1:8000");
    let public_key = "020202020202020202020202020202020202020202020202020202020202020202"
        .parse::<bitcoin::PublicKey>()
        .unwrap();
    let socket = String::from("127.0.0.1");
    let time_hash_set = TimeVec(Vec::new());
    let parent_hash_set: HashSet<BlockHash> = HashSet::new();
    //Adding test txid
    let test_txid =
        Txid::from_str("8df401c7580ea2491d88d936ed0e16f3e6ea6c3d69eb9d9cf27652696a559e24").unwrap();
    let weak_target = CompactTarget::from_consensus(32);
    let min_target = CompactTarget::from_consensus(1);
    let time_val = Time::from_consensus(1653195600).unwrap();
    let test_committed_metadata = TestCommittedMetadataBuilder::new()
        .comm_pub_key(public_key)
        .miner_ip(socket)
        .start_timestamp(time_val)
        .parents(parent_hash_set)
        .parent_bead_timestamps(time_hash_set)
        .payout_address(_address)
        .min_target(min_target)
        .weak_target(weak_target)
        .transactions(vec![test_txid])
        .build();
    let extra_nonce = 42;
    let hex = "3046022100839c1fbc5304de944f697c9f4b1d01d1faeba32d751c0f7acb21ac8a0f436a72022100e89bd46bb3a5a62adc679f659b7ce876d83ee297c7a5587b2011c4fcc72eab45";
    let sig = Signature {
        signature: secp256k1::ecdsa::Signature::from_str(hex).unwrap(),
        sighash_type: EcdsaSighashType::All,
    };
    let test_uncommitted_metadata = TestUnCommittedMetadataBuilder::new()
        .broadcast_timestamp(time_val)
        .extra_nonce(extra_nonce, extra_nonce)
        .signature(sig)
        .build();
    let test_bytes: [u8; 32] = [0u8; 32];
    let test_block_header = BlockHeader {
        version: BlockVersion::TWO,
        prev_blockhash: BlockHash::from_byte_array(test_bytes),
        bits: CompactTarget::from_consensus(32),
        nonce: 1,
        time: BlockTime::from_u32(8328429),
        merkle_root: TxMerkleNode::from_byte_array(test_bytes),
    };
    let test_bead = TestBeadBuilder::new()
        .block_header(test_block_header)
        .committed_metadata(test_committed_metadata)
        .uncommitted_metadata(test_uncommitted_metadata)
        .build();
    let serialized_val = serialize(&test_bead);
    let deserialized_result: Result<Bead, DeserializeError> = deserialize(&serialized_val);
    let deserialized_bead = match deserialized_result {
        Ok(val) => val,
        Err(error) => {
            panic!("An error occurred while deserializaing bead {:?}", error);
        }
    };
    println!("{:?}  ", deserialized_bead);
    assert_eq!(deserialized_bead, test_bead);
}

#[test]
fn test_bead_request_serialization() {
    let request = BeadRequest::GetBeads(
        vec![BeadHash::from_byte_array([0u8; 32])]
            .into_iter()
            .collect(),
    );
    let mut buffer = Vec::new();
    request.consensus_encode(&mut buffer).unwrap();

    let decoded = BeadRequest::consensus_decode(&mut buffer.as_slice()).unwrap();
    assert_eq!(request, decoded);
}

#[test]
fn test_bead_response_serialization() {
    let _address = String::from("127.0.0.1:8000");
    let public_key = "020202020202020202020202020202020202020202020202020202020202020202"
        .parse::<bitcoin::PublicKey>()
        .unwrap();
    let socket = String::from("127.0.0.1");
    let time_hash_set = TimeVec(Vec::new());
    let parent_hash_set: HashSet<BlockHash> = HashSet::new();
    let weak_target = CompactTarget::from_unprefixed_hex("1d00ffff").unwrap();
    let min_target = CompactTarget::from_unprefixed_hex("1d00ffff").unwrap();
    let time_val = Time::from_consensus(1653195600).unwrap();
    let test_committed_metadata = TestCommittedMetadataBuilder::new()
        .comm_pub_key(public_key)
        .miner_ip(socket)
        .start_timestamp(time_val)
        .parents(parent_hash_set)
        .parent_bead_timestamps(time_hash_set)
        .payout_address(_address)
        .min_target(min_target)
        .weak_target(weak_target)
        .transactions(vec![])
        .build();
    let extra_nonce = 42;
    let hex = "3046022100839c1fbc5304de944f697c9f4b1d01d1faeba32d751c0f7acb21ac8a0f436a72022100e89bd46bb3a5a62adc679f659b7ce876d83ee297c7a5587b2011c4fcc72eab45";
    let sig = Signature {
        signature: secp256k1::ecdsa::Signature::from_str(hex).unwrap(),
        sighash_type: EcdsaSighashType::All,
    };
    let test_uncommitted_metadata = TestUnCommittedMetadataBuilder::new()
        .broadcast_timestamp(time_val)
        .extra_nonce(extra_nonce, extra_nonce)
        .signature(sig)
        .build();
    let test_bytes: [u8; 32] = [0u8; 32];
    let test_block_header = BlockHeader {
        version: BlockVersion::TWO,
        prev_blockhash: BlockHash::from_byte_array(test_bytes),
        bits: CompactTarget::from_consensus(32),
        nonce: 1,
        time: BlockTime::from_u32(8328429),
        merkle_root: TxMerkleNode::from_byte_array(test_bytes),
    };
    let test_bead = TestBeadBuilder::new()
        .block_header(test_block_header)
        .committed_metadata(test_committed_metadata)
        .uncommitted_metadata(test_uncommitted_metadata)
        .build();
    let response = BeadResponse::Beads(vec![test_bead]);
    let mut buffer = Vec::new();
    response.consensus_encode(&mut buffer).unwrap();
    let decoded = BeadResponse::consensus_decode(&mut buffer.as_slice()).unwrap();
    assert_eq!(response, decoded);
}

#[test]
fn test_codec_request_roundtrip() {
    let mut codec = BeadCodec::default();
    let request = BeadRequest::GetTips;

    // Serialize
    let mut buffer = Vec::new();
    request.consensus_encode(&mut buffer).unwrap();
    let io = Cursor::new(buffer);

    // Deserialize
    let protocol = libp2p::StreamProtocol::new("/braidpool/1.0.0");
    let decoded_request =
        block_on(codec.read_request(&protocol, &mut futures::io::AllowStdIo::new(io))).unwrap();
    assert_eq!(request, decoded_request);
}

#[test]
fn test_codec_response_roundtrip() {
    let mut codec = BeadCodec::default();
    let response = BeadResponse::Tips(
        vec![
            BeadHash::from_byte_array([
                3, 4, 5, 6, 7, 8, 9, 10, 1, 2, 3, 4, 5, 1, 24, 12, 14, 35, 35, 34, 3, 42, 32, 32,
                32, 32, 4, 32, 24, 5, 12, 1,
            ]),
            BeadHash::from_byte_array([
                1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1, 2, 3, 4, 5, 6, 7, 8, 9, 1,
                2, 3, 4, 5,
            ]),
        ]
        .into_iter()
        .collect(),
    );

    // Serialize
    let mut buffer = Vec::new();
    response.consensus_encode(&mut buffer).unwrap();
    let io = Cursor::new(buffer);
    // Deserialize
    let protocol = libp2p::StreamProtocol::new("/braidpool/1.0.0");
    let decoded_response =
        block_on(codec.read_response(&protocol, &mut futures::io::AllowStdIo::new(io))).unwrap();
    assert_eq!(response, decoded_response);
}

#[test]
fn test_get_beads_after_serialization() {
    let mut codec = BeadCodec::default();
    let request = BeadRequest::GetBeadsAfter(
        vec![BeadHash::from_byte_array([0u8; 32])]
            .into_iter()
            .collect(),
    );

    // Serialize
    let mut buffer = Vec::new();
    request.consensus_encode(&mut buffer).unwrap();
    let io = Cursor::new(buffer);

    // Deserialize
    let protocol = libp2p::StreamProtocol::new("/braidpool/1.0.0");
    let decoded_request =
        block_on(codec.read_request(&protocol, &mut futures::io::AllowStdIo::new(io))).unwrap();
    assert_eq!(request, decoded_request);
}

// test codec for all bead request types
#[test]
fn test_bead_request_codec() {
    let mut codec = BeadCodec::default();

    for request in vec![
        BeadRequest::GetTips,
        BeadRequest::GetBeads(Vec::from([BeadHash::from_byte_array([0u8; 32])])),
        BeadRequest::GetGenesis,
        BeadRequest::GetAllBeads,
        BeadRequest::GetBeadsAfter(vec![BeadHash::from_byte_array([0u8; 32])]),
    ] {
        // Serialize
        let mut buffer = Vec::new();
        request.consensus_encode(&mut buffer).unwrap();
        let io = Cursor::new(buffer);

        // Deserialize
        let protocol = libp2p::StreamProtocol::new("/braidpool/1.0.0");
        let decoded_request =
            block_on(codec.read_request(&protocol, &mut futures::io::AllowStdIo::new(io))).unwrap();
        assert_eq!(request, decoded_request);
    }
}

#[test]
fn test_bead_response_codec() {
    let mut codec = BeadCodec::default();

    // Create test bead for responses that need beads
    let test_bead = create_test_bead(1, None);
    let test_hash = BeadHash::from_byte_array([1u8; 32]);
    let test_hash2 = BeadHash::from_byte_array([2u8; 32]);

    // Test all BeadResponse variants
    let responses = vec![
        BeadResponse::Beads(vec![test_bead.clone()]),
        BeadResponse::Tips(vec![test_hash, test_hash2]),
        BeadResponse::Genesis(vec![test_hash]),
        BeadResponse::GetAllBeads(vec![test_bead.clone(), test_bead.clone()]),
        BeadResponse::GetBeadsAfter(vec![test_bead.clone()]),
        BeadResponse::Error(BeadSyncError::GenesisMismatch),
        BeadResponse::Error(BeadSyncError::Other("Test error message".to_string())),
    ];

    for response in responses {
        // Serialize
        let mut buffer = Vec::new();
        response.consensus_encode(&mut buffer).unwrap();
        let io = Cursor::new(buffer);

        // Deserialize
        let protocol = libp2p::StreamProtocol::new("/braidpool/1.0.0");
        let decoded_response =
            block_on(codec.read_response(&protocol, &mut futures::io::AllowStdIo::new(io)))
                .unwrap();
        assert_eq!(response, decoded_response);
    }
}

#[test]
fn test_bead_sync_error_codec() {
    // Test BeadSyncError encoding/decoding directly (not through codec)
    let errors = vec![
        BeadSyncError::GenesisMismatch,
        BeadSyncError::Other("Network timeout".to_string()),
        BeadSyncError::Other("Invalid bead format".to_string()),
        BeadSyncError::Other("".to_string()), // Empty string edge case
        BeadSyncError::Other("Very long error message that tests the string encoding and decoding with special characters: !@#$%^&*()_+-=[]{}|;':,.<>?".to_string()),
    ];

    for error in errors {
        // Serialize
        let mut buffer = Vec::new();
        error.consensus_encode(&mut buffer).unwrap();

        // Deserialize
        let mut cursor = Cursor::new(buffer);
        let decoded_error = BeadSyncError::consensus_decode(&mut cursor).unwrap();
        assert_eq!(error, decoded_error);
    }

    // Test invalid error type decoding
    let mut invalid_buffer = Vec::new();
    255u8.consensus_encode(&mut invalid_buffer).unwrap(); // Invalid error type
    let mut cursor = Cursor::new(invalid_buffer);
    let result = BeadSyncError::consensus_decode(&mut cursor);
    assert!(result.is_err(), "Should fail to decode invalid error type");
}
