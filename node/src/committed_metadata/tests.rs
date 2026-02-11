use super::*;
use crate::utils::test_utils::test_utility_functions::TestCommittedMetadataBuilder;
use bitcoin::absolute::MedianTimePast;
use bitcoin::consensus::encode::deserialize;
use bitcoin::consensus::serialize;
use bitcoin::BlockHash;
use std::collections::HashSet;
use std::str::FromStr;

#[test]
fn test_timevec_roundtrip_empty() {
    let original = TimeVec(vec![]);
    let bytes = serialize(&original);
    let decoded: TimeVec = deserialize(&bytes).unwrap();
    assert_eq!(original, decoded);
}

#[test]
fn test_timevec_roundtrip_single() {
    let time = Time::from_consensus(1653195600).unwrap();
    let original = TimeVec(vec![time]);
    let bytes = serialize(&original);
    let decoded: TimeVec = deserialize(&bytes).unwrap();
    assert_eq!(original, decoded);
}

#[test]
fn test_timevec_roundtrip_multiple() {
    let times = vec![
        Time::from_consensus(1653195600).unwrap(),
        Time::from_consensus(1653195700).unwrap(),
        Time::from_consensus(1653195800).unwrap(),
    ];
    let original = TimeVec(times);
    let bytes = serialize(&original);
    let decoded: TimeVec = deserialize(&bytes).unwrap();
    assert_eq!(original, decoded);
}

#[test]
fn test_txidvec_roundtrip_empty() {
    let original = TxIdVec(vec![]);
    let bytes = serialize(&original);
    let decoded: TxIdVec = deserialize(&bytes).unwrap();
    assert_eq!(original, decoded);
}

#[test]
fn test_txidvec_roundtrip_single() {
    let txid =
        Txid::from_str("4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b").unwrap();
    let original = TxIdVec(vec![txid]);
    let bytes = serialize(&original);
    let decoded: TxIdVec = deserialize(&bytes).unwrap();
    assert_eq!(original, decoded);
}

#[test]
fn test_txidvec_roundtrip_multiple() {
    let txids = vec![
        Txid::from_str("4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b").unwrap(),
        Txid::from_str("0e3e2357e806b6cdb1f70b54c3a3a17b6714ee1f0e68bebb44a74b1efd512098").unwrap(),
        Txid::from_str("9b0fc92260312ce44e74ef369f5c66bbb85848f2eddd5a7a1cde251e54ccfdd5").unwrap(),
    ];
    let original = TxIdVec(txids);
    let bytes = serialize(&original);
    let decoded: TxIdVec = deserialize(&bytes).unwrap();
    assert_eq!(original, decoded);
}

#[test]
fn test_committed_metadata_default() {
    let metadata = CommittedMetadata::default();

    assert_eq!(metadata.transaction_ids, TxIdVec(Vec::new()));
    assert!(metadata.parents.is_empty());
    assert_eq!(metadata.parent_bead_timestamps, TimeVec(Vec::new()));
    assert_eq!(metadata.payout_address, "bc1");
    assert_eq!(metadata.start_timestamp, MedianTimePast::MIN);
    assert_eq!(
        metadata.comm_pub_key,
        PublicKey::from_str("020202020202020202020202020202020202020202020202020202020202020202")
            .unwrap()
    );
    assert_eq!(
        metadata.min_target,
        CompactTarget::from_consensus(486604799)
    );
    assert_eq!(
        metadata.weak_target,
        CompactTarget::from_consensus(486604799)
    );
    assert_eq!(metadata.miner_ip, "127.0.0.1");
}

#[test]
fn test_committed_metadata_roundtrip_default() {
    let original = CommittedMetadata::default();
    let bytes = serialize(&original);
    let decoded: CommittedMetadata = deserialize(&bytes).unwrap();
    assert_eq!(original, decoded);
}

#[test]
fn test_committed_metadata_roundtrip_populated() {
    let public_key =
        PublicKey::from_str("020202020202020202020202020202020202020202020202020202020202020202")
            .unwrap();

    let txids = vec![
        Txid::from_str("4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b").unwrap(),
        Txid::from_str("0e3e2357e806b6cdb1f70b54c3a3a17b6714ee1f0e68bebb44a74b1efd512098").unwrap(),
    ];

    let parent1 =
        BlockHash::from_str("000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f")
            .unwrap();
    let parent2 =
        BlockHash::from_str("00000000839a8e6886ab5951d76f411475428afc90947ee320161bbf18eb6048")
            .unwrap();
    let mut parents = HashSet::new();
    parents.insert(parent1);
    parents.insert(parent2);

    let timestamps = TimeVec(vec![
        Time::from_consensus(1653195600).unwrap(),
        Time::from_consensus(1653195700).unwrap(),
    ]);

    let original = TestCommittedMetadataBuilder::new()
        .transactions(txids)
        .parents(parents)
        .parent_bead_timestamps(timestamps)
        .payout_address("bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4".to_string())
        .start_timestamp(Time::from_consensus(1653195600).unwrap())
        .comm_pub_key(public_key)
        .min_target(CompactTarget::from_consensus(486604799))
        .weak_target(CompactTarget::from_consensus(486604799))
        .miner_ip("192.168.1.100".to_string())
        .build();

    let bytes = serialize(&original);
    let decoded: CommittedMetadata = deserialize(&bytes).unwrap();
    assert_eq!(original, decoded);
}

#[test]
fn test_committed_metadata_deterministic_parent_encoding() {
    let parent1 =
        BlockHash::from_str("000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f")
            .unwrap();
    let parent2 =
        BlockHash::from_str("00000000839a8e6886ab5951d76f411475428afc90947ee320161bbf18eb6048")
            .unwrap();
    let parent3 =
        BlockHash::from_str("000000006a625f06636b8bb6ac7b960a8d03705d1ace08b1a19da3fdcc99ddbd")
            .unwrap();

    let public_key =
        PublicKey::from_str("020202020202020202020202020202020202020202020202020202020202020202")
            .unwrap();

    // Build the same metadata multiple times — HashSet iteration order is
    // non-deterministic, but the encoded bytes must always be identical
    // because hashset_to_vec_deterministic sorts the parents.
    let mut encodings = Vec::new();
    for _ in 0..5 {
        let mut parents = HashSet::new();
        parents.insert(parent1);
        parents.insert(parent2);
        parents.insert(parent3);

        let metadata = TestCommittedMetadataBuilder::new()
            .transactions(vec![])
            .parents(parents)
            .parent_bead_timestamps(TimeVec(vec![]))
            .payout_address("bc1".to_string())
            .start_timestamp(Time::from_consensus(1653195600).unwrap())
            .comm_pub_key(public_key)
            .min_target(CompactTarget::from_consensus(486604799))
            .weak_target(CompactTarget::from_consensus(486604799))
            .miner_ip("127.0.0.1".to_string())
            .build();

        encodings.push(serialize(&metadata));
    }

    // All 5 serializations must be byte-identical.
    for encoding in &encodings[1..] {
        assert_eq!(
            &encodings[0], encoding,
            "parent encoding is not deterministic"
        );
    }
}

#[test]
fn test_committed_metadata_serde_json_roundtrip() {
    let public_key =
        PublicKey::from_str("020202020202020202020202020202020202020202020202020202020202020202")
            .unwrap();

    let txid =
        Txid::from_str("4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b").unwrap();

    let parent =
        BlockHash::from_str("000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f")
            .unwrap();
    let mut parents = HashSet::new();
    parents.insert(parent);

    let original = TestCommittedMetadataBuilder::new()
        .transactions(vec![txid])
        .parents(parents)
        .parent_bead_timestamps(TimeVec(vec![Time::from_consensus(1653195600).unwrap()]))
        .payout_address("bc1qw508d6qejxtdg4y5r3zarvary0c5xw7kv8f3t4".to_string())
        .start_timestamp(Time::from_consensus(1653195600).unwrap())
        .comm_pub_key(public_key)
        .min_target(CompactTarget::from_consensus(486604799))
        .weak_target(CompactTarget::from_consensus(486604799))
        .miner_ip("10.0.0.1".to_string())
        .build();

    let json = serde_json::to_string(&original).expect("serialize to JSON");
    let decoded: CommittedMetadata = serde_json::from_str(&json).expect("deserialize from JSON");
    assert_eq!(original, decoded);
}
