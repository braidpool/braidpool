//! Wire and JSON format of `UnCommittedMetadata`: a 64-byte BIP340 Schnorr signature, never an
//! ECDSA DER signature.

use super::UnCommittedMetadata;
use bitcoin::absolute::Time;
use bitcoin::consensus::{deserialize, serialize, Encodable};

fn sample() -> UnCommittedMetadata {
    UnCommittedMetadata {
        extra_nonce_1: 7,
        extra_nonce_2: 9,
        broadcast_timestamp: Time::from_consensus(1_700_000_000).unwrap(),
        ..UnCommittedMetadata::default()
    }
}

/// ECDSA DER signature plus sighash byte, as the previous encoding stored it (hex string).
const OLD_DER_SIGNATURE_HEX: &str = "3046022100839c1fbc5304de944f697c9f4b1d01d1faeba32d751c0f7acb21ac8a0f436a72022100e89bd46bb3a5a62adc679f659b7ce876d83ee297c7a5587b2011c4fcc72eab4501";

#[test]
fn consensus_roundtrip_and_fixed_length() {
    let metadata = sample();
    let bytes = serialize(&metadata);
    // 8 + 8 (extranonces) + 4 (timestamp) + 64 (Schnorr signature), no length prefixes.
    assert_eq!(bytes.len(), 84);
    let decoded: UnCommittedMetadata = deserialize(&bytes).unwrap();
    assert_eq!(decoded, metadata);
}

#[test]
fn legacy_der_signature_encoding_is_rejected() {
    let mut old = Vec::new();
    7u64.consensus_encode(&mut old).unwrap();
    9u64.consensus_encode(&mut old).unwrap();
    1_700_000_000u32.consensus_encode(&mut old).unwrap();
    // The old encoding wrote the signature as a length-prefixed string.
    OLD_DER_SIGNATURE_HEX
        .to_string()
        .consensus_encode(&mut old)
        .unwrap();
    assert!(deserialize::<UnCommittedMetadata>(&old).is_err());
}

#[test]
fn truncated_signature_is_rejected() {
    let mut bytes = serialize(&sample());
    bytes.truncate(bytes.len() - 1);
    assert!(deserialize::<UnCommittedMetadata>(&bytes).is_err());
}

#[test]
fn trailing_bytes_after_the_signature_are_rejected() {
    // For example a leftover sighash-type byte.
    let mut bytes = serialize(&sample());
    bytes.push(0x01);
    assert!(deserialize::<UnCommittedMetadata>(&bytes).is_err());
}

#[test]
fn json_signature_is_128_hex_characters() {
    let json = serde_json::to_value(sample()).unwrap();
    let signature = json["signature"].as_str().unwrap();
    assert_eq!(signature.len(), 128);
    assert!(signature.chars().all(|c| c.is_ascii_hexdigit()));
}

#[test]
fn json_der_signature_is_rejected() {
    let mut json = serde_json::to_value(sample()).unwrap();
    json["signature"] = serde_json::Value::String(OLD_DER_SIGNATURE_HEX.to_string());
    assert!(serde_json::from_value::<UnCommittedMetadata>(json).is_err());
}
