use super::*;
use crate::utils::test_utils::test_utility_functions::TestUnCommittedMetadataBuilder;
use bitcoin::absolute::MedianTimePast;
use bitcoin::consensus::encode::deserialize;
use bitcoin::consensus::serialize;
use bitcoin::ecdsa::Signature;
use bitcoin::EcdsaSighashType;
use serde::Deserialize;
use std::fs;
use std::path::Path;
use std::str::FromStr;
use std::sync::OnceLock;

const TEST_DATA_PATH: &str = "../tests/test_data.json";

#[derive(Debug, Deserialize)]
struct TestData {
    uncommitted_metadata: UnCommittedMetadataTestData,
}

#[derive(Debug, Deserialize)]
struct UnCommittedMetadataTestData {
    nonces: NoncesData,
    timestamps: TimestampsData,
    signatures: SignaturesData,
}

#[derive(Debug, Deserialize)]
struct NoncesData {
    default_nonce_1: u32,
    default_nonce_2: u32,
    populated_nonce_1: u32,
    populated_nonce_2: u32,
}

#[derive(Debug, Deserialize)]
struct TimestampsData {
    first: u32,
    second: u32,
}

#[derive(Debug, Deserialize)]
struct SignaturesData {
    default_hex: String,
    alternate_hex: String,
}

fn test_data() -> &'static UnCommittedMetadataTestData {
    static TEST_DATA: OnceLock<TestData> = OnceLock::new();
    &TEST_DATA
        .get_or_init(|| {
            let path = Path::new(env!("CARGO_MANIFEST_DIR")).join(TEST_DATA_PATH);
            let content = fs::read_to_string(&path)
                .unwrap_or_else(|e| panic!("failed reading {}: {}", path.display(), e));
            serde_json::from_str(&content)
                .unwrap_or_else(|e| panic!("failed parsing {}: {}", path.display(), e))
        })
        .uncommitted_metadata
}

fn parse_time(value: u32) -> Time {
    Time::from_consensus(value).unwrap()
}

fn parse_signature(hex: &str) -> Signature {
    Signature {
        signature: secp256k1::ecdsa::Signature::from_str(hex).unwrap(),
        sighash_type: EcdsaSighashType::All,
    }
}

#[test]
fn test_uncommitted_metadata_default() {
    let data = test_data();
    let metadata = UnCommittedMetadata::default();

    assert_eq!(metadata.extra_nonce_1, data.nonces.default_nonce_1);
    assert_eq!(metadata.extra_nonce_2, data.nonces.default_nonce_2);
    assert_eq!(metadata.broadcast_timestamp, MedianTimePast::MIN);
    assert_eq!(
        metadata.signature,
        parse_signature(&data.signatures.default_hex)
    );
}

#[test]
fn test_uncommitted_metadata_roundtrip_default() {
    let original = UnCommittedMetadata::default();
    let bytes = serialize(&original);
    let decoded: UnCommittedMetadata = deserialize(&bytes).unwrap();
    assert_eq!(original, decoded);
}

#[test]
fn test_uncommitted_metadata_roundtrip_populated() {
    let data = test_data();

    let original = TestUnCommittedMetadataBuilder::new()
        .extra_nonce(data.nonces.populated_nonce_1, data.nonces.populated_nonce_2)
        .broadcast_timestamp(parse_time(data.timestamps.first))
        .signature(parse_signature(&data.signatures.alternate_hex))
        .build();

    let bytes = serialize(&original);
    let decoded: UnCommittedMetadata = deserialize(&bytes).unwrap();
    assert_eq!(original, decoded);
}

#[test]
fn test_uncommitted_metadata_serde_json_roundtrip() {
    let data = test_data();

    let original = TestUnCommittedMetadataBuilder::new()
        .extra_nonce(data.nonces.populated_nonce_1, data.nonces.populated_nonce_2)
        .broadcast_timestamp(parse_time(data.timestamps.first))
        .signature(parse_signature(&data.signatures.default_hex))
        .build();

    let json = serde_json::to_string(&original).expect("serialize to JSON");
    let decoded: UnCommittedMetadata = serde_json::from_str(&json).expect("deserialize from JSON");
    assert_eq!(original, decoded);
}

#[test]
fn test_uncommitted_metadata_consensus_field_order_decode() {
    let data = test_data();

    let metadata = TestUnCommittedMetadataBuilder::new()
        .extra_nonce(data.nonces.populated_nonce_1, data.nonces.populated_nonce_2)
        .broadcast_timestamp(parse_time(data.timestamps.first))
        .signature(parse_signature(&data.signatures.default_hex))
        .build();

    let bytes = serialize(&metadata);
    let mut reader = &bytes[..];

    // Decode each field manually in the expected encoding order
    let decoded_extra_nonce_1 = u32::consensus_decode(&mut reader).unwrap();
    let decoded_extra_nonce_2 = u32::consensus_decode(&mut reader).unwrap();
    let decoded_broadcast_timestamp =
        Time::from_consensus(u32::consensus_decode(&mut reader).unwrap()).unwrap();
    let decoded_signature =
        Signature::from_str(&String::consensus_decode(&mut reader).unwrap()).unwrap();

    assert_eq!(decoded_extra_nonce_1, data.nonces.populated_nonce_1);
    assert_eq!(decoded_extra_nonce_2, data.nonces.populated_nonce_2);
    assert_eq!(
        decoded_broadcast_timestamp,
        parse_time(data.timestamps.first)
    );
    assert_eq!(
        decoded_signature,
        parse_signature(&data.signatures.default_hex)
    );
    assert!(reader.is_empty(), "consensus decode left trailing bytes");
}

#[test]
fn test_uncommitted_metadata_deterministic_encoding() {
    let data = test_data();

    let mut encodings = Vec::new();
    for _ in 0..5 {
        let metadata = TestUnCommittedMetadataBuilder::new()
            .extra_nonce(data.nonces.populated_nonce_1, data.nonces.populated_nonce_2)
            .broadcast_timestamp(parse_time(data.timestamps.first))
            .signature(parse_signature(&data.signatures.default_hex))
            .build();

        encodings.push(serialize(&metadata));
    }

    for encoding in &encodings[1..] {
        assert_eq!(&encodings[0], encoding, "encoding is not deterministic");
    }
}

#[test]
fn test_uncommitted_metadata_different_nonces_different_encoding() {
    let data = test_data();
    let ts = parse_time(data.timestamps.first);

    let metadata_a = TestUnCommittedMetadataBuilder::new()
        .extra_nonce(data.nonces.populated_nonce_1, data.nonces.populated_nonce_2)
        .broadcast_timestamp(ts)
        .signature(parse_signature(&data.signatures.default_hex))
        .build();

    let metadata_b = TestUnCommittedMetadataBuilder::new()
        .extra_nonce(
            data.nonces.populated_nonce_1 + 1,
            data.nonces.populated_nonce_2,
        )
        .broadcast_timestamp(ts)
        .signature(parse_signature(&data.signatures.default_hex))
        .build();

    assert_ne!(
        serialize(&metadata_a),
        serialize(&metadata_b),
        "different nonces must produce different encoding"
    );
}

#[test]
fn test_uncommitted_metadata_different_timestamps_different_encoding() {
    let data = test_data();

    let metadata_a = TestUnCommittedMetadataBuilder::new()
        .extra_nonce(data.nonces.populated_nonce_1, data.nonces.populated_nonce_2)
        .broadcast_timestamp(parse_time(data.timestamps.first))
        .signature(parse_signature(&data.signatures.default_hex))
        .build();

    let metadata_b = TestUnCommittedMetadataBuilder::new()
        .extra_nonce(data.nonces.populated_nonce_1, data.nonces.populated_nonce_2)
        .broadcast_timestamp(parse_time(data.timestamps.second))
        .signature(parse_signature(&data.signatures.default_hex))
        .build();

    assert_ne!(
        serialize(&metadata_a),
        serialize(&metadata_b),
        "different timestamps must produce different encoding"
    );
}

#[test]
fn test_uncommitted_metadata_different_signatures_different_encoding() {
    let data = test_data();
    let ts = parse_time(data.timestamps.first);

    let metadata_a = TestUnCommittedMetadataBuilder::new()
        .extra_nonce(data.nonces.populated_nonce_1, data.nonces.populated_nonce_2)
        .broadcast_timestamp(ts)
        .signature(parse_signature(&data.signatures.default_hex))
        .build();

    let metadata_b = TestUnCommittedMetadataBuilder::new()
        .extra_nonce(data.nonces.populated_nonce_1, data.nonces.populated_nonce_2)
        .broadcast_timestamp(ts)
        .signature(parse_signature(&data.signatures.alternate_hex))
        .build();

    assert_ne!(
        serialize(&metadata_a),
        serialize(&metadata_b),
        "different signatures must produce different encoding"
    );
}
