use super::*;
use crate::utils::hashset_to_vec_deterministic;
use crate::utils::test_utils::test_utility_functions::TestCommittedMetadataBuilder;
use bitcoin::absolute::MedianTimePast;
use bitcoin::consensus::encode::deserialize;
use bitcoin::consensus::serialize;
use bitcoin::BlockHash;
use serde::Deserialize;
use std::collections::HashSet;
use std::fs;
use std::path::Path;
use std::str::FromStr;
use std::sync::OnceLock;

#[derive(Debug, Deserialize)]
struct TestData {
    committed_metadata: CommittedMetadataTestData,
}

#[derive(Debug, Deserialize)]
struct CommittedMetadataTestData {
    txids: TxidsData,
    block_hashes: BlockHashesData,
    timestamps: TimestampsData,
    public_keys: PublicKeysData,
    targets: TargetsData,
    payout_addresses: PayoutAddressesData,
    miner_ips: MinerIpsData,
}

#[derive(Debug, Deserialize)]
struct TxidsData {
    genesis: String,
    second: String,
    third: String,
}

#[derive(Debug, Deserialize)]
struct BlockHashesData {
    parent1: String,
    parent2: String,
    parent3: String,
}

#[derive(Debug, Deserialize)]
struct TimestampsData {
    first: u32,
    second: u32,
    third: u32,
}

#[derive(Debug, Deserialize)]
struct PublicKeysData {
    default_committed: String,
}

#[derive(Debug, Deserialize)]
struct TargetsData {
    default_bits: u32,
}

#[derive(Debug, Deserialize)]
struct PayoutAddressesData {
    default: String,
    populated: String,
}

#[derive(Debug, Deserialize)]
struct MinerIpsData {
    loopback: String,
    lan: String,
    internal: String,
}

fn test_data() -> &'static CommittedMetadataTestData {
    static TEST_DATA: OnceLock<TestData> = OnceLock::new();
    &TEST_DATA
        .get_or_init(|| {
            let path = Path::new(env!("CARGO_MANIFEST_DIR")).join("../tests/test_data.json");
            let content = fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("failed reading {}: {}", path.display(), e));
            serde_json::from_str(&content)
                .unwrap_or_else(|e| panic!("failed parsing {}: {}", path.display(), e))
        })
        .committed_metadata
}

fn parse_txid(value: &str) -> Txid {
    Txid::from_str(value).unwrap()
}

fn parse_block_hash(value: &str) -> BlockHash {
    BlockHash::from_str(value).unwrap()
}

fn parse_time(value: u32) -> Time {
    Time::from_consensus(value).unwrap()
}

fn parse_public_key(value: &str) -> PublicKey {
    PublicKey::from_str(value).unwrap()
}

fn parse_target(value: u32) -> CompactTarget {
    CompactTarget::from_consensus(value)
}

#[test]
fn test_timevec_roundtrip_empty() {
    let original = TimeVec(vec![]);
    let bytes = serialize(&original);
    let decoded: TimeVec = deserialize(&bytes).unwrap();
    assert_eq!(original, decoded);
}

#[test]
fn test_timevec_roundtrip_single() {
    let data = test_data();
    let time = parse_time(data.timestamps.first);
    let original = TimeVec(vec![time]);
    let bytes = serialize(&original);
    let decoded: TimeVec = deserialize(&bytes).unwrap();
    assert_eq!(original, decoded);
}

#[test]
fn test_timevec_roundtrip_multiple() {
    let data = test_data();
    let times = vec![
        parse_time(data.timestamps.first),
        parse_time(data.timestamps.second),
        parse_time(data.timestamps.third),
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
    let data = test_data();
    let txid = parse_txid(&data.txids.genesis);
    let original = TxIdVec(vec![txid]);
    let bytes = serialize(&original);
    let decoded: TxIdVec = deserialize(&bytes).unwrap();
    assert_eq!(original, decoded);
}

#[test]
fn test_txidvec_roundtrip_multiple() {
    let data = test_data();
    let txids = vec![
        parse_txid(&data.txids.genesis),
        parse_txid(&data.txids.second),
        parse_txid(&data.txids.third),
    ];
    let original = TxIdVec(txids);
    let bytes = serialize(&original);
    let decoded: TxIdVec = deserialize(&bytes).unwrap();
    assert_eq!(original, decoded);
}

#[test]
fn test_committed_metadata_default() {
    let data = test_data();
    let metadata = CommittedMetadata::default();

    assert_eq!(metadata.transaction_ids, TxIdVec(Vec::new()));
    assert!(metadata.parents.is_empty());
    assert_eq!(metadata.parent_bead_timestamps, TimeVec(Vec::new()));
    assert_eq!(
        metadata.payout_address,
        data.payout_addresses.default.as_str()
    );
    assert_eq!(metadata.start_timestamp, MedianTimePast::MIN);
    assert_eq!(
        metadata.comm_pub_key,
        parse_public_key(&data.public_keys.default_committed)
    );
    assert_eq!(metadata.min_target, parse_target(data.targets.default_bits));
    assert_eq!(
        metadata.weak_target,
        parse_target(data.targets.default_bits)
    );
    assert_eq!(metadata.miner_ip, data.miner_ips.loopback.as_str());
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
    let data = test_data();
    let public_key = parse_public_key(&data.public_keys.default_committed);

    let txids = vec![
        parse_txid(&data.txids.genesis),
        parse_txid(&data.txids.second),
    ];

    let parent1 = parse_block_hash(&data.block_hashes.parent1);
    let parent2 = parse_block_hash(&data.block_hashes.parent2);
    let mut parents = HashSet::new();
    parents.insert(parent1);
    parents.insert(parent2);

    let timestamps = TimeVec(vec![
        parse_time(data.timestamps.first),
        parse_time(data.timestamps.second),
    ]);

    let original = TestCommittedMetadataBuilder::new()
        .transactions(txids)
        .parents(parents)
        .parent_bead_timestamps(timestamps)
        .payout_address(data.payout_addresses.populated.clone())
        .start_timestamp(parse_time(data.timestamps.first))
        .comm_pub_key(public_key)
        .min_target(parse_target(data.targets.default_bits))
        .weak_target(parse_target(data.targets.default_bits))
        .miner_ip(data.miner_ips.lan.clone())
        .build();

    let bytes = serialize(&original);
    let decoded: CommittedMetadata = deserialize(&bytes).unwrap();
    assert_eq!(original, decoded);
}

#[test]
fn test_committed_metadata_deterministic_parent_encoding() {
    let data = test_data();
    let parent1 = parse_block_hash(&data.block_hashes.parent1);
    let parent2 = parse_block_hash(&data.block_hashes.parent2);
    let parent3 = parse_block_hash(&data.block_hashes.parent3);

    let public_key = parse_public_key(&data.public_keys.default_committed);

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
            .payout_address(data.payout_addresses.default.clone())
            .start_timestamp(parse_time(data.timestamps.first))
            .comm_pub_key(public_key)
            .min_target(parse_target(data.targets.default_bits))
            .weak_target(parse_target(data.targets.default_bits))
            .miner_ip(data.miner_ips.loopback.clone())
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
    let data = test_data();
    let public_key = parse_public_key(&data.public_keys.default_committed);

    let txid = parse_txid(&data.txids.genesis);

    let parent = parse_block_hash(&data.block_hashes.parent1);
    let mut parents = HashSet::new();
    parents.insert(parent);

    let original = TestCommittedMetadataBuilder::new()
        .transactions(vec![txid])
        .parents(parents)
        .parent_bead_timestamps(TimeVec(vec![parse_time(data.timestamps.first)]))
        .payout_address(data.payout_addresses.populated.clone())
        .start_timestamp(parse_time(data.timestamps.first))
        .comm_pub_key(public_key)
        .min_target(parse_target(data.targets.default_bits))
        .weak_target(parse_target(data.targets.default_bits))
        .miner_ip(data.miner_ips.internal.clone())
        .build();

    let json = serde_json::to_string(&original).expect("serialize to JSON");
    let decoded: CommittedMetadata = serde_json::from_str(&json).expect("deserialize from JSON");
    assert_eq!(original, decoded);
}

#[test]
fn test_committed_metadata_consensus_field_order_decode() {
    let data = test_data();
    let public_key = parse_public_key(&data.public_keys.default_committed);
    let txids = vec![
        parse_txid(&data.txids.genesis),
        parse_txid(&data.txids.second),
    ];

    let mut parents = HashSet::new();
    parents.insert(parse_block_hash(&data.block_hashes.parent2));
    parents.insert(parse_block_hash(&data.block_hashes.parent1));
    parents.insert(parse_block_hash(&data.block_hashes.parent3));

    let metadata = TestCommittedMetadataBuilder::new()
        .transactions(txids.clone())
        .parents(parents.clone())
        .parent_bead_timestamps(TimeVec(vec![
            parse_time(data.timestamps.first),
            parse_time(data.timestamps.second),
            parse_time(data.timestamps.third),
        ]))
        .payout_address(data.payout_addresses.populated.clone())
        .start_timestamp(parse_time(data.timestamps.first))
        .comm_pub_key(public_key)
        .min_target(parse_target(data.targets.default_bits))
        .weak_target(parse_target(data.targets.default_bits))
        .miner_ip(data.miner_ips.lan.clone())
        .build();

    let bytes = serialize(&metadata);
    let mut reader = &bytes[..];

    let decoded_txids = TxIdVec::consensus_decode(&mut reader).unwrap();
    let decoded_parents = Vec::<BeadHash>::consensus_decode(&mut reader).unwrap();
    let decoded_parent_times = TimeVec::consensus_decode(&mut reader).unwrap();
    let decoded_payout = String::consensus_decode(&mut reader).unwrap();
    let decoded_start_timestamp =
        Time::from_consensus(u32::consensus_decode(&mut reader).unwrap()).unwrap();
    let decoded_pubkey =
        PublicKey::from_slice(&Vec::<u8>::consensus_decode(&mut reader).unwrap()).unwrap();
    let decoded_min_target = CompactTarget::consensus_decode(&mut reader).unwrap();
    let decoded_weak_target = CompactTarget::consensus_decode(&mut reader).unwrap();
    let decoded_miner_ip = String::consensus_decode(&mut reader).unwrap();

    assert_eq!(decoded_txids, TxIdVec(txids));
    assert_eq!(decoded_parents, hashset_to_vec_deterministic(&parents));
    assert_eq!(
        decoded_parent_times,
        TimeVec(vec![
            parse_time(data.timestamps.first),
            parse_time(data.timestamps.second),
            parse_time(data.timestamps.third),
        ])
    );
    assert_eq!(decoded_payout, data.payout_addresses.populated);
    assert_eq!(decoded_start_timestamp, parse_time(data.timestamps.first));
    assert_eq!(
        decoded_pubkey,
        parse_public_key(&data.public_keys.default_committed)
    );
    assert_eq!(decoded_min_target, parse_target(data.targets.default_bits));
    assert_eq!(decoded_weak_target, parse_target(data.targets.default_bits));
    assert_eq!(decoded_miner_ip, data.miner_ips.lan);
    assert!(reader.is_empty(), "consensus decode left trailing bytes");
}

#[test]
fn test_committed_metadata_consensus_parents_are_canonical() {
    let data = test_data();
    let public_key = parse_public_key(&data.public_keys.default_committed);

    let parent1 = parse_block_hash(&data.block_hashes.parent1);
    let parent2 = parse_block_hash(&data.block_hashes.parent2);
    let parent3 = parse_block_hash(&data.block_hashes.parent3);

    let mut parents = HashSet::new();
    parents.insert(parent3);
    parents.insert(parent1);
    parents.insert(parent2);

    let metadata = TestCommittedMetadataBuilder::new()
        .transactions(vec![])
        .parents(parents.clone())
        .parent_bead_timestamps(TimeVec(vec![]))
        .payout_address(data.payout_addresses.default.clone())
        .start_timestamp(parse_time(data.timestamps.first))
        .comm_pub_key(public_key)
        .min_target(parse_target(data.targets.default_bits))
        .weak_target(parse_target(data.targets.default_bits))
        .miner_ip(data.miner_ips.loopback.clone())
        .build();

    let bytes = serialize(&metadata);
    let mut reader = &bytes[..];
    let _ = TxIdVec::consensus_decode(&mut reader).unwrap();
    let decoded_parents = Vec::<BeadHash>::consensus_decode(&mut reader).unwrap();

    assert_eq!(decoded_parents, hashset_to_vec_deterministic(&parents));
}

#[test]
fn test_committed_metadata_consensus_txid_order_is_significant() {
    let data = test_data();
    let public_key = parse_public_key(&data.public_keys.default_committed);
    let txid_a = parse_txid(&data.txids.genesis);
    let txid_b = parse_txid(&data.txids.second);

    let mut parents = HashSet::new();
    parents.insert(parse_block_hash(&data.block_hashes.parent1));

    let metadata_ab = TestCommittedMetadataBuilder::new()
        .transactions(vec![txid_a, txid_b])
        .parents(parents.clone())
        .parent_bead_timestamps(TimeVec(vec![parse_time(data.timestamps.first)]))
        .payout_address(data.payout_addresses.populated.clone())
        .start_timestamp(parse_time(data.timestamps.first))
        .comm_pub_key(public_key)
        .min_target(parse_target(data.targets.default_bits))
        .weak_target(parse_target(data.targets.default_bits))
        .miner_ip(data.miner_ips.internal.clone())
        .build();

    let metadata_ba = TestCommittedMetadataBuilder::new()
        .transactions(vec![txid_b, txid_a])
        .parents(parents)
        .parent_bead_timestamps(TimeVec(vec![parse_time(data.timestamps.first)]))
        .payout_address(data.payout_addresses.populated.clone())
        .start_timestamp(parse_time(data.timestamps.first))
        .comm_pub_key(public_key)
        .min_target(parse_target(data.targets.default_bits))
        .weak_target(parse_target(data.targets.default_bits))
        .miner_ip(data.miner_ips.internal.clone())
        .build();

    assert_ne!(serialize(&metadata_ab), serialize(&metadata_ba));
}
