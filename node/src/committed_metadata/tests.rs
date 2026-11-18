use super::*;
use crate::utils::test_utils::test_utility_functions::TestCommittedMetadataBuilder;
use bitcoin::consensus::encode::deserialize;
use bitcoin::consensus::serialize;
use bitcoin::hashes::Hash;
use bitcoin::BlockHash;
use serde::Deserialize;
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

    assert_eq!(metadata.coinbase_transaction, placeholder_coinbase());
    assert_eq!(metadata.committed_txs, TxIdVec(Vec::new()));
    assert_eq!(metadata.to_be_added, TxIdVec(Vec::new()));
    assert!(metadata.parents.is_empty());
    assert_eq!(metadata.parent_bead_timestamps, TimeVec(Vec::new()));
    assert_eq!(
        metadata.payout_address,
        data.payout_addresses.default.as_str()
    );
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
    let mut parents = vec![parent1, parent2];
    parents.sort();

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
        let mut parents = vec![parent1, parent2, parent3];
        parents.sort();

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
    let parents = vec![parent];
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

    let mut parents = vec![
        parse_block_hash(&data.block_hashes.parent2),
        parse_block_hash(&data.block_hashes.parent1),
        parse_block_hash(&data.block_hashes.parent3),
    ];
    parents.sort();

    let to_be_added = vec![parse_txid(&data.txids.third)];

    let metadata = TestCommittedMetadataBuilder::new()
        .transactions(txids.clone())
        .to_be_added(to_be_added.clone())
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
        .fee_total_sats(12_345_678)
        .build();

    let bytes = serialize(&metadata);
    let mut reader = &bytes[..];

    let decoded_coinbase = Transaction::consensus_decode(&mut reader).unwrap();
    let decoded_txids = TxIdVec::consensus_decode(&mut reader).unwrap();
    let decoded_to_be_added = TxIdVec::consensus_decode(&mut reader).unwrap();
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
    let decoded_fee_total_sats = u64::consensus_decode(&mut reader).unwrap();

    assert_eq!(decoded_coinbase, placeholder_coinbase());
    assert_eq!(decoded_txids, TxIdVec(txids));
    assert_eq!(decoded_to_be_added, TxIdVec(to_be_added));
    assert_eq!(decoded_parents, parents);
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
    assert_eq!(decoded_fee_total_sats, 12_345_678);
    assert!(reader.is_empty(), "consensus decode left trailing bytes");
}

#[test]
fn test_committed_metadata_consensus_parents_are_canonical() {
    let data = test_data();
    let public_key = parse_public_key(&data.public_keys.default_committed);

    let parent1 = parse_block_hash(&data.block_hashes.parent1);
    let parent2 = parse_block_hash(&data.block_hashes.parent2);
    let parent3 = parse_block_hash(&data.block_hashes.parent3);

    let mut parents = vec![parent3, parent1, parent2];
    parents.sort();

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
    let _ = Transaction::consensus_decode(&mut reader).unwrap();
    let _ = TxIdVec::consensus_decode(&mut reader).unwrap();
    let _ = TxIdVec::consensus_decode(&mut reader).unwrap();
    let decoded_parents = Vec::<BeadHash>::consensus_decode(&mut reader).unwrap();

    assert_eq!(decoded_parents, parents);
}

#[test]
fn test_committed_metadata_consensus_txid_order_is_significant() {
    let data = test_data();
    let public_key = parse_public_key(&data.public_keys.default_committed);
    let txid_a = parse_txid(&data.txids.genesis);
    let txid_b = parse_txid(&data.txids.second);

    let parents = vec![parse_block_hash(&data.block_hashes.parent1)];

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

/// A coinbase with one output, distinct from the placeholder.
fn sample_coinbase() -> Transaction {
    let mut coinbase = placeholder_coinbase();
    coinbase.input[0].script_sig = bitcoin::ScriptBuf::from_bytes(vec![0x01, 0x64]);
    coinbase.output.push(bitcoin::TxOut {
        value: bitcoin::Amount::from_sat(5_000_000_000),
        script_pubkey: bitcoin::ScriptBuf::new(),
    });
    coinbase
}

/// A txid whose first four bytes are `value`.
fn numbered_txid(value: u32) -> Txid {
    let mut bytes = [0u8; 32];
    bytes[..4].copy_from_slice(&value.to_le_bytes());
    Txid::from_byte_array(bytes)
}

// The coinbase and both transaction lists survive a consensus round trip, and
// the two lists are kept apart.
#[test]
fn test_committed_metadata_roundtrip_coinbase_and_tx_lists() {
    let data = test_data();
    let original = CommittedMetadata {
        coinbase_transaction: sample_coinbase(),
        committed_txs: TxIdVec(vec![
            parse_txid(&data.txids.genesis),
            parse_txid(&data.txids.second),
        ]),
        to_be_added: TxIdVec(vec![parse_txid(&data.txids.third)]),
        ..CommittedMetadata::default()
    };

    let decoded: CommittedMetadata = deserialize(&serialize(&original)).unwrap();

    assert_eq!(decoded, original);
    assert_eq!(decoded.coinbase_transaction, sample_coinbase());
    assert_eq!(decoded.committed_txs.0.len(), 2);
    assert_eq!(
        decoded.to_be_added,
        TxIdVec(vec![parse_txid(&data.txids.third)])
    );
}

// A bead may propose at most MAX_TO_BE_ADDED_TXS transactions; one more is
// refused by the decoder.
#[test]
fn test_committed_metadata_rejects_too_many_to_be_added() {
    let at_limit = CommittedMetadata {
        to_be_added: TxIdVec((0..MAX_TO_BE_ADDED_TXS as u32).map(numbered_txid).collect()),
        ..CommittedMetadata::default()
    };
    let over_limit = CommittedMetadata {
        to_be_added: TxIdVec(
            (0..=MAX_TO_BE_ADDED_TXS as u32)
                .map(numbered_txid)
                .collect(),
        ),
        ..CommittedMetadata::default()
    };

    assert!(deserialize::<CommittedMetadata>(&serialize(&at_limit)).is_ok());
    assert!(deserialize::<CommittedMetadata>(&serialize(&over_limit)).is_err());
}

// A txid repeated within either transaction list is refused by the decoder.
#[test]
fn test_committed_metadata_rejects_duplicate_txids() {
    let duplicate_committed = CommittedMetadata {
        committed_txs: TxIdVec(vec![numbered_txid(1), numbered_txid(2), numbered_txid(1)]),
        ..CommittedMetadata::default()
    };
    let duplicate_to_be_added = CommittedMetadata {
        to_be_added: TxIdVec(vec![numbered_txid(1), numbered_txid(1)]),
        ..CommittedMetadata::default()
    };

    assert!(deserialize::<CommittedMetadata>(&serialize(&duplicate_committed)).is_err());
    assert!(deserialize::<CommittedMetadata>(&serialize(&duplicate_to_be_added)).is_err());
}

// A declared length beyond the limit is refused before anything is allocated
// or read, so a tiny message cannot reserve memory.
#[test]
fn test_txidvec_rejects_oversized_declared_length() {
    let bytes = serialize(&u64::MAX);

    assert!(TxIdVec::consensus_decode(&mut &bytes[..]).is_err());
    assert!(TxIdVec::consensus_decode_bounded(&mut &bytes[..], MAX_TO_BE_ADDED_TXS).is_err());
}

// A declared length within the limit but with no elements behind it fails on
// the missing data instead of allocating for the declared count.
#[test]
fn test_txidvec_rejects_truncated_list() {
    let bytes = serialize(&(MAX_COMMITTED_TXS as u64));

    assert!(TxIdVec::consensus_decode(&mut &bytes[..]).is_err());
}

// A parent timestamp that is not a valid block time is a decode error, not a
// panic, and a huge declared length does not allocate.
#[test]
fn test_timevec_rejects_invalid_timestamp_and_oversized_length() {
    let mut invalid_time = serialize(&1u64);
    invalid_time.extend(serialize(&0u32));
    let oversized = serialize(&u64::MAX);

    assert!(TimeVec::consensus_decode(&mut &invalid_time[..]).is_err());
    assert!(TimeVec::consensus_decode(&mut &oversized[..]).is_err());
}
