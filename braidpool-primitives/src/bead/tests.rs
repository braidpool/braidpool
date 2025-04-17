use ::bitcoin::BlockHash;
use ::bitcoin::Network;
use bitcoin::BlockTime;
use bitcoin::BlockVersion;
use bitcoin::CompactTarget;
use bitcoin::EcdsaSighashType;
use bitcoin::absolute::Time;
use bitcoin::address::NetworkChecked;
use bitcoin::base58::Error;
use bitcoin::ecdsa::Signature;
use bitcoin::hashes::sha256t::Hash;
use bitcoin::secp256k1::PublicKey;
use bitcoin::transaction::TransactionExt;
use bitcoin::{Address, Block, TxMerkleNode};
use bitcoin::{BlockHeader, Transaction};
use core::net::SocketAddr;
use secp256k1::Message;
use secp256k1::{Secp256k1, SecretKey};
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde_json::json;
use std::collections::HashSet;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
use std::str::FromStr;

use super::Bead;
use super::CommittedMetadata;
use super::UnCommittedMetadata;
#[test]

fn test_serialized_bead() {
    let _address: Address = Address::from_str("32iVBEu4dxkUQk9dJbZUiBiQdmypcEyJRf")
        .unwrap()
        .require_network(Network::Bitcoin)
        .unwrap();
    let secp = Secp256k1::new();
    let secret_key = SecretKey::from_byte_array(&[0xcd; 32]).expect("32 bytes, within curve order");
    let public_key = PublicKey::from_secret_key(&secp, &secret_key);
    let socket = SocketAddr::new(IpAddr::V4(Ipv4Addr::new(127, 0, 0, 1)), 8080);

    let test_committed_metadata = CommittedMetadata {
        transaction_cnt: 0,
        parents: HashSet::new(),
        transactions: vec![],
        payout_address: _address,
        comm_pub_key: public_key,
        observed_time_at_node: Time::from_consensus(1653195600).unwrap(),
        miner_ip: socket,
    };
    let hex = "3046022100839c1fbc5304de944f697c9f4b1d01d1faeba32d751c0f7acb21ac8a0f436a72022100e89bd46bb3a5a62adc679f659b7ce876d83ee297c7a5587b2011c4fcc72eab45";
    let sig = Signature {
        signature: secp256k1::ecdsa::Signature::from_str(hex).unwrap(),
        sighash_type: EcdsaSighashType::All,
    };

    let test_uncommittedmetadata: UnCommittedMetadata = UnCommittedMetadata {
        extra_nonce: 12,
        broadcast_timestamp: Time::from_consensus(1653195600).unwrap(),
        signature: sig,
        parent_bead_timestamps: HashSet::new(),
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
        committed_metadata: test_committed_metadata,
        uncommitted_metadata: test_uncommittedmetadata,
    };
    let serialized_str = serde_json::to_string(&test_bead).unwrap();
    assert_eq!(
        serialized_str,
        r#"{"block_header":{"version":2,"prev_blockhash":"0000000000000000000000000000000000000000000000000000000000000000","merkle_root":"0000000000000000000000000000000000000000000000000000000000000000","time":8328429,"bits":32,"nonce":1},"committed_metadata":{"transaction_cnt":0,"transactions":[],"parents":[],"payout_address":"32iVBEu4dxkUQk9dJbZUiBiQdmypcEyJRf","observed_time_at_node":1653195600,"comm_pub_key":"02b98a7fb8cc007048625b6446ad49a1b3a722df8c1ca975b87160023e14d19097","miner_ip":"127.0.0.1:8080"},"uncommitted_metadata":{"extra_nonce":12,"broadcast_timestamp":1653195600,"signature":{"signature":"3046022100839c1fbc5304de944f697c9f4b1d01d1faeba32d751c0f7acb21ac8a0f436a72022100e89bd46bb3a5a62adc679f659b7ce876d83ee297c7a5587b2011c4fcc72eab45","sighash_type":"SIGHASH_ALL"},"parent_bead_timestamps":[]}}"#
    );
}
