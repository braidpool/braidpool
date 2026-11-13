//! BIP340 Schnorr signatures over uncommitted bead metadata.
//!
//! The signed message is a tagged hash (`Braidpool/bead/uncommitted/v1`) of the
//! uncommitted fields plus the block header and committed metadata, so a valid
//! signature cannot be transplanted onto a different bead.

use crate::bead::Bead;
use crate::braid::{AddBeadStatus, Braid};
use bitcoin::consensus::encode::Encodable;
use bitcoin::hashes::{sha256, Hash, HashEngine};
use bitcoin::secp256k1::schnorr::Signature as SchnorrSignature;
use bitcoin::secp256k1::{Keypair, Message, Secp256k1, SecretKey};
use bitcoin::XOnlyPublicKey;
use rand::rngs::OsRng;
use rand::RngCore;
use std::fmt;

/// Domain-separation tag for uncommitted-metadata Schnorr signatures.
pub const UNCOMMITTED_SIGHASH_TAG: &[u8] = b"Braidpool/bead/uncommitted/v1";

/// Errors while signing or verifying a bead's uncommitted Schnorr signature.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BeadSignError {
    /// Consensus encoding of signed fields failed.
    Encode(String),
    /// The Schnorr signature does not match `comm_pub_key`.
    InvalidSignature,
    /// The signing secret is not the secret of the bead's `comm_pub_key`, so the signature
    /// would never verify. Holds the x-only key of the signing secret; the bead's own key is
    /// on the bead.
    KeyMismatch(XOnlyPublicKey),
    /// The operating system's random number generator failed to produce the BIP340
    /// auxiliary randomness.
    Randomness(String),
}

impl fmt::Display for BeadSignError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            BeadSignError::Encode(e) => write!(f, "failed to encode bead sighash payload: {e}"),
            BeadSignError::InvalidSignature => {
                write!(f, "invalid Schnorr signature on uncommitted metadata")
            }
            BeadSignError::KeyMismatch(signer) => {
                write!(f, "signing key {signer} is not the bead's comm_pub_key")
            }
            BeadSignError::Randomness(e) => {
                write!(f, "failed to draw BIP340 auxiliary randomness: {e}")
            }
        }
    }
}

impl std::error::Error for BeadSignError {}

/// BIP340 tagged hash: SHA256(SHA256(tag) || SHA256(tag) || msg).
pub fn tagged_hash(tag: &[u8], msg: &[u8]) -> [u8; 32] {
    let tag_hash = sha256::Hash::hash(tag);
    let mut engine = sha256::Hash::engine();
    engine.input(tag_hash.as_byte_array());
    engine.input(tag_hash.as_byte_array());
    engine.input(msg);
    sha256::Hash::from_engine(engine).to_byte_array()
}

/// Consensus payload covered by the uncommitted Schnorr signature.
pub fn uncommitted_sighash_payload(bead: &Bead) -> Result<Vec<u8>, BeadSignError> {
    let mut payload = Vec::new();
    bead.uncommitted_metadata
        .extra_nonce_1
        .consensus_encode(&mut payload)
        .map_err(|e| BeadSignError::Encode(e.to_string()))?;
    bead.uncommitted_metadata
        .extra_nonce_2
        .consensus_encode(&mut payload)
        .map_err(|e| BeadSignError::Encode(e.to_string()))?;
    bead.uncommitted_metadata
        .broadcast_timestamp
        .to_consensus_u32()
        .consensus_encode(&mut payload)
        .map_err(|e| BeadSignError::Encode(e.to_string()))?;
    bead.block_header
        .consensus_encode(&mut payload)
        .map_err(|e| BeadSignError::Encode(e.to_string()))?;
    bead.committed_metadata
        .consensus_encode(&mut payload)
        .map_err(|e| BeadSignError::Encode(e.to_string()))?;
    Ok(payload)
}

/// Digest passed to BIP340 sign/verify.
pub fn uncommitted_sighash(bead: &Bead) -> Result<[u8; 32], BeadSignError> {
    Ok(tagged_hash(
        UNCOMMITTED_SIGHASH_TAG,
        &uncommitted_sighash_payload(bead)?,
    ))
}

/// Sign `bead.uncommitted_metadata` with `secret`, using 32 bytes of fresh auxiliary
/// randomness from the operating system as BIP340 recommends.
///
/// Does not change `comm_pub_key`, which must already be the x-only key of `secret`.
///
/// # Arguments
/// * `bead` - The bead to sign. Only `uncommitted_metadata.signature` is written.
/// * `secret` - The secret of the bead's `comm_pub_key`.
pub fn sign_uncommitted_metadata(bead: &mut Bead, secret: &SecretKey) -> Result<(), BeadSignError> {
    let mut aux_rand = [0u8; 32];
    OsRng
        .try_fill_bytes(&mut aux_rand)
        .map_err(|e| BeadSignError::Randomness(e.to_string()))?;
    sign_uncommitted_metadata_with_aux_rand(bead, secret, &aux_rand)
}

/// [`sign_uncommitted_metadata`] with caller-supplied auxiliary randomness.
///
/// A fixed `aux_rand` makes the signature deterministic, which tests rely on. Production
/// code signs through [`sign_uncommitted_metadata`] so every signature gets fresh randomness,
/// the BIP340 hardening against side-channel and fault attacks on the nonce.
fn sign_uncommitted_metadata_with_aux_rand(
    bead: &mut Bead,
    secret: &SecretKey,
    aux_rand: &[u8; 32],
) -> Result<(), BeadSignError> {
    let secp = Secp256k1::signing_only();
    let keypair = Keypair::from_secret_key(&secp, secret);
    let (signer, _) = keypair.x_only_public_key();
    if signer != bead.committed_metadata.comm_pub_key {
        return Err(BeadSignError::KeyMismatch(signer));
    }
    let msg = Message::from_digest(uncommitted_sighash(bead)?);
    bead.uncommitted_metadata.signature = secp.sign_schnorr_with_aux_rand(&msg, &keypair, aux_rand);
    Ok(())
}

/// Verify `bead.uncommitted_metadata.signature` against `comm_pub_key`.
pub fn verify_uncommitted_signature(bead: &Bead) -> Result<(), BeadSignError> {
    let digest = uncommitted_sighash(bead)?;
    let secp = Secp256k1::verification_only();
    let msg = Message::from_digest(digest);
    secp.verify_schnorr(
        &bead.uncommitted_metadata.signature,
        &msg,
        &bead.committed_metadata.comm_pub_key,
    )
    .map_err(|_| BeadSignError::InvalidSignature)
}

/// A bead whose Schnorr signature is valid under its own `comm_pub_key`.
///
/// [`Braid::extend_verified`] accepts only this type and `Braid::extend` is crate-private, so
/// outside this crate a bead cannot reach the DAG without passing through [`VerifiedBead::new`].
#[derive(Debug, Clone, Copy)]
pub struct VerifiedBead<'a>(&'a Bead);

impl<'a> VerifiedBead<'a> {
    /// Verify `bead`'s signature.
    pub fn new(bead: &'a Bead) -> Result<Self, BeadSignError> {
        verify_uncommitted_signature(bead)?;
        Ok(Self(bead))
    }

    /// The verified bead.
    pub fn bead(&self) -> &'a Bead {
        self.0
    }
}

/// Verify `bead` and extend the DAG with it, or return `InvalidBead` if verification fails.
pub fn extend_verified(braid: &mut Braid, bead: &Bead) -> AddBeadStatus {
    match VerifiedBead::new(bead) {
        Ok(verified) => braid.extend_verified(verified),
        Err(e) => {
            tracing::debug!(error = %e, "Rejected bead with invalid signature");
            AddBeadStatus::InvalidBead
        }
    }
}

/// Parse a committed miner pubkey: must be exactly 32 valid x-only bytes.
pub fn parse_xonly_pubkey(bytes: &[u8]) -> Result<XOnlyPublicKey, String> {
    if bytes.len() != 32 {
        return Err(format!(
            "comm_pub_key must be 32 bytes (x-only), got {}",
            bytes.len()
        ));
    }
    XOnlyPublicKey::from_slice(bytes).map_err(|e| format!("invalid x-only comm_pub_key: {e}"))
}

/// Parse a BIP340 Schnorr signature: must be exactly 64 bytes.
pub fn parse_schnorr_signature(bytes: &[u8]) -> Result<SchnorrSignature, String> {
    SchnorrSignature::from_slice(bytes)
        .map_err(|e| format!("invalid Schnorr signature ({} bytes): {e}", bytes.len()))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::miner_identity::MinerIdentity;
    use crate::utils::create_test_bead;
    use bitcoin::consensus::{deserialize, serialize};

    #[test]
    fn sign_verify_roundtrip() {
        let identity = MinerIdentity::generate();
        let mut bead = create_test_bead(1, None);
        bead.committed_metadata.comm_pub_key = identity.xonly();
        sign_uncommitted_metadata(&mut bead, identity.secret_for_tests()).unwrap();
        verify_uncommitted_signature(&bead).unwrap();
    }

    #[test]
    fn rejects_wrong_signer() {
        let signer = MinerIdentity::generate();
        let other = MinerIdentity::generate();
        let mut bead = create_test_bead(1, None);
        bead.committed_metadata.comm_pub_key = other.xonly();
        // `sign_uncommitted_metadata` refuses this, so sign the sighash directly.
        let secp = Secp256k1::new();
        let keypair = Keypair::from_secret_key(&secp, signer.secret_for_tests());
        let msg = Message::from_digest(uncommitted_sighash(&bead).unwrap());
        bead.uncommitted_metadata.signature =
            secp.sign_schnorr_with_aux_rand(&msg, &keypair, &[0; 32]);
        assert_eq!(
            verify_uncommitted_signature(&bead),
            Err(BeadSignError::InvalidSignature)
        );
    }

    #[test]
    fn signing_refuses_a_secret_that_does_not_own_comm_pub_key() {
        let signer = MinerIdentity::generate();
        let other = MinerIdentity::generate();
        let mut bead = create_test_bead(1, None);
        bead.committed_metadata.comm_pub_key = other.xonly();
        let before = bead.clone();
        assert_eq!(
            sign_uncommitted_metadata(&mut bead, signer.secret_for_tests()),
            Err(BeadSignError::KeyMismatch(signer.xonly()))
        );
        assert_eq!(bead, before, "a refused signing must not touch the bead");
    }

    #[test]
    fn signing_accepts_the_negated_secret_of_comm_pub_key() {
        // A secret and its negation share one x-only key; both are valid BIP340 signers.
        let identity = MinerIdentity::generate();
        let mut bead = create_test_bead(1, None);
        bead.committed_metadata.comm_pub_key = identity.xonly();
        sign_uncommitted_metadata(&mut bead, &identity.secret_for_tests().negate()).unwrap();
        verify_uncommitted_signature(&bead).unwrap();
    }

    #[test]
    fn each_signature_uses_fresh_aux_randomness() {
        let identity = MinerIdentity::generate();
        let mut first = create_test_bead(1, None);
        first.committed_metadata.comm_pub_key = identity.xonly();
        let mut second = first.clone();
        sign_uncommitted_metadata(&mut first, identity.secret_for_tests()).unwrap();
        sign_uncommitted_metadata(&mut second, identity.secret_for_tests()).unwrap();
        assert_ne!(
            first.uncommitted_metadata.signature,
            second.uncommitted_metadata.signature
        );
        verify_uncommitted_signature(&first).unwrap();
        verify_uncommitted_signature(&second).unwrap();
    }

    #[test]
    fn fixed_aux_randomness_is_deterministic() {
        let identity = MinerIdentity::generate();
        let mut first = create_test_bead(1, None);
        first.committed_metadata.comm_pub_key = identity.xonly();
        let mut second = first.clone();
        let aux_rand = [7u8; 32];
        sign_uncommitted_metadata_with_aux_rand(&mut first, identity.secret_for_tests(), &aux_rand)
            .unwrap();
        sign_uncommitted_metadata_with_aux_rand(
            &mut second,
            identity.secret_for_tests(),
            &aux_rand,
        )
        .unwrap();
        assert_eq!(
            first.uncommitted_metadata.signature,
            second.uncommitted_metadata.signature
        );
        verify_uncommitted_signature(&first).unwrap();
    }

    #[test]
    fn rejects_transplanted_signature() {
        let identity = MinerIdentity::generate();
        let mut bead_a = create_test_bead(1, None);
        bead_a.committed_metadata.comm_pub_key = identity.xonly();
        sign_uncommitted_metadata(&mut bead_a, identity.secret_for_tests()).unwrap();

        let mut bead_b = create_test_bead(2, None);
        bead_b.committed_metadata.comm_pub_key = identity.xonly();
        bead_b.uncommitted_metadata.signature = bead_a.uncommitted_metadata.signature;
        assert_eq!(
            verify_uncommitted_signature(&bead_b),
            Err(BeadSignError::InvalidSignature)
        );
    }

    #[test]
    fn parse_xonly_rejects_compressed_pubkey() {
        let compressed =
            hex::decode("020202020202020202020202020202020202020202020202020202020202020202")
                .unwrap();
        assert!(parse_xonly_pubkey(&compressed).is_err());
    }

    #[test]
    fn parse_schnorr_rejects_der() {
        let der = hex::decode(
            "3046022100839c1fbc5304de944f697c9f4b1d01d1faeba32d751c0f7acb21ac8a0f436a72022100e89bd46bb3a5a62adc679f659b7ce876d83ee297c7a5587b2011c4fcc72eab45",
        )
        .unwrap();
        assert!(parse_schnorr_signature(&der).is_err());
    }

    #[test]
    fn extend_verified_rejects_unsigned() {
        let mut braid = crate::braid::Braid::new(Vec::new(), crate::config::PoolNetwork::Cpunet);
        let bead = create_test_bead(1, None);
        let mut unsigned = bead.clone();
        unsigned.uncommitted_metadata.signature = SchnorrSignature::from_slice(&[0u8; 64]).unwrap();
        assert!(matches!(
            extend_verified(&mut braid, &unsigned),
            AddBeadStatus::InvalidBead
        ));
        assert!(matches!(
            extend_verified(&mut braid, &bead),
            AddBeadStatus::BeadAdded { .. }
        ));
    }

    #[test]
    fn consensus_roundtrip_xonly_and_schnorr() {
        let identity = MinerIdentity::generate();
        let mut bead = create_test_bead(1, None);
        bead.committed_metadata.comm_pub_key = identity.xonly();
        sign_uncommitted_metadata(&mut bead, identity.secret_for_tests()).unwrap();
        let bytes = serialize(&bead);
        let decoded: Bead = deserialize(&bytes).unwrap();
        assert_eq!(decoded, bead);
        verify_uncommitted_signature(&decoded).unwrap();
    }
}
