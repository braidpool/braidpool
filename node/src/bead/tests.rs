use super::Bead;
use super::CommittedMetadata;
use super::UnCommittedMetadata;
use crate::uncommitted_metadata::TimeVec;
use crate::utils::test_utils::test_utility_functions::*;
use bitcoin::absolute::Time;
use bitcoin::consensus::encode::deserialize;
use bitcoin::consensus::serialize;
use bitcoin::consensus::DeserializeError;
use bitcoin::ecdsa::Signature;
use bitcoin::p2p::Address as P2P_Address;
use bitcoin::p2p::ServiceFlags;
use bitcoin::BlockHash;
use bitcoin::BlockHeader;
use bitcoin::BlockTime;
use bitcoin::BlockVersion;
use bitcoin::CompactTarget;
use bitcoin::EcdsaSighashType;
use bitcoin::TxMerkleNode;
use core::net::SocketAddr;
use std::collections::HashSet;
use std::net::{IpAddr, Ipv4Addr};
use std::str::FromStr;
#[test]

fn test_serialized_committed_metadata() {
    let test_sock_add = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8888);
    let _address = P2P_Address::new(&test_sock_add.clone(), ServiceFlags::NONE);
    let public_key = "020202020202020202020202020202020202020202020202020202020202020202"
        .parse::<bitcoin::PublicKey>()
        .unwrap();
    let socket = bitcoin::p2p::address::AddrV2::Ipv4(Ipv4Addr::new(127, 0, 0, 1));
    let time_val = Time::from_consensus(1653195600).unwrap();
    let parent_hash_set: HashSet<BlockHash> = HashSet::new();
    let weak_target = CompactTarget::from_consensus(32);
    let min_target = CompactTarget::from_consensus(1);
    let test_committed_metadata = TestCommittedMetadataBuilder::new()
        .comm_pub_key(public_key)
        .miner_ip(socket)
        .start_timestamp(time_val)
        .parents(parent_hash_set)
        .payout_address(_address)
        .transaction_cnt(0)
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
    let time_hash_set = TimeVec(Vec::new());
    let extra_nonce = 42;
    let test_uncommitted_metadata = TestUnCommittedMetadataBuilder::new()
        .broadcast_timestamp(time_val)
        .extra_nonce(extra_nonce)
        .parent_bead_timestamps(time_hash_set)
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
    let test_sock_add = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8888);
    let _address = P2P_Address::new(&test_sock_add.clone(), ServiceFlags::NONE);
    let public_key = "020202020202020202020202020202020202020202020202020202020202020202"
        .parse::<bitcoin::PublicKey>()
        .unwrap();
    let socket = bitcoin::p2p::address::AddrV2::Ipv4(Ipv4Addr::new(127, 0, 0, 1));
    let time_hash_set = TimeVec(Vec::new());
    let parent_hash_set: HashSet<BlockHash> = HashSet::new();
    let weak_target = CompactTarget::from_consensus(32);
    let min_target = CompactTarget::from_consensus(1);
    let time_val = Time::from_consensus(1653195600).unwrap();
    let test_committed_metadata = TestCommittedMetadataBuilder::new()
        .comm_pub_key(public_key)
        .miner_ip(socket)
        .start_timestamp(time_val)
        .parents(parent_hash_set)
        .payout_address(_address)
        .transaction_cnt(0)
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
        .extra_nonce(extra_nonce)
        .parent_bead_timestamps(time_hash_set)
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
