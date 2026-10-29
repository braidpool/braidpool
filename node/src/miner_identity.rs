//! Per-node secp256k1 miner identity used for BIP340 bead signatures.
//!
//! The secret is stored at `datadir/miner_secp256k1` (see [`crate::secret_file`]). It is the
//! node's whole identity: the BIP340 x-only key committed in every bead, and the secp256k1 key
//! behind the libp2p `PeerId` (see [`MinerIdentity::libp2p_keypair`]).

use crate::bead::sign::{sign_uncommitted_metadata, BeadSignError};
use crate::bead::Bead;
use crate::secret_file::read_or_create_secret;
use bitcoin::secp256k1::{Secp256k1, SecretKey};
use bitcoin::XOnlyPublicKey;
use rand::rngs::OsRng;
use std::fmt;
use std::io::{self, ErrorKind};
use std::path::{Path, PathBuf};
use tracing::info;

/// File name of the secp256k1 miner secret in the data directory.
pub const MINER_SECP256K1_FILENAME: &str = "miner_secp256k1";

/// secp256k1 key used as `CommittedMetadata.comm_pub_key` and to Schnorr-sign
/// uncommitted metadata.
#[derive(Clone)]
pub struct MinerIdentity {
    secret: SecretKey,
    xonly: XOnlyPublicKey,
}

impl fmt::Debug for MinerIdentity {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("MinerIdentity")
            .field("xonly", &self.xonly)
            .finish_non_exhaustive()
    }
}

impl MinerIdentity {
    /// Deterministic identity for tests that need a shared `comm_pub_key`.
    pub fn test_fixture() -> Self {
        let mut bytes = [0u8; 32];
        bytes[31] = 1;
        Self::from_secret(
            SecretKey::from_slice(&bytes).expect("integer 1 is a valid secp256k1 secret"),
        )
    }

    /// Generate a fresh miner identity (tests and first-run keystore).
    pub fn generate() -> Self {
        let secp = Secp256k1::new();
        let (secret, _) = secp.generate_keypair(&mut OsRng);
        Self::from_secret(secret)
    }

    /// Build identity from an existing secret.
    pub fn from_secret(secret: SecretKey) -> Self {
        let secp = Secp256k1::new();
        let keypair = bitcoin::secp256k1::Keypair::from_secret_key(&secp, &secret);
        let (xonly, _) = keypair.x_only_public_key();
        Self { secret, xonly }
    }

    /// Load `datadir/miner_secp256k1`, or create it with a fresh secret if it does not exist.
    ///
    /// # Errors
    /// Any error from [`read_or_create_secret`], or a file that is not exactly 32 bytes holding
    /// a valid secret scalar. An invalid file is left untouched.
    pub fn load_or_generate(datadir: impl AsRef<Path>) -> io::Result<Self> {
        let path = miner_key_path(datadir.as_ref());
        let (bytes, created) = read_or_create_secret(&path, || {
            Ok(Self::generate().secret.secret_bytes().to_vec())
        })?;
        if bytes.len() != 32 {
            return Err(io::Error::new(
                ErrorKind::InvalidData,
                format!(
                    "miner secp256k1 key at {} must be 32 bytes, got {}",
                    path.display(),
                    bytes.len()
                ),
            ));
        }
        let secret = SecretKey::from_slice(&bytes).map_err(|e| {
            io::Error::new(
                ErrorKind::InvalidData,
                format!("invalid miner secp256k1 secret at {}: {e}", path.display()),
            )
        })?;
        if created {
            info!(path = %path.display(), "Generated miner secp256k1 identity");
        } else {
            info!(path = %path.display(), "Loaded miner secp256k1 identity");
        }
        Ok(Self::from_secret(secret))
    }

    /// X-only public key committed in every bead this node forms.
    pub fn xonly(&self) -> XOnlyPublicKey {
        self.xonly
    }

    /// Secret for tests that must sign without setting `comm_pub_key`.
    #[cfg(test)]
    pub(crate) fn secret_for_tests(&self) -> &SecretKey {
        &self.secret
    }

    /// Set `comm_pub_key` to this identity and sign uncommitted metadata.
    pub fn sign_bead(&self, bead: &mut Bead) -> Result<(), BeadSignError> {
        bead.committed_metadata.comm_pub_key = self.xonly;
        sign_uncommitted_metadata(bead, &self.secret)
    }

    /// The libp2p keypair for this node, derived from the miner secret.
    ///
    /// libp2p's secp256k1 key is an ECDSA key, so the transport stays ECDSA; what is shared is
    /// the secret. The secret is normalised to its even-y form first, so the public key always
    /// starts with `02`, its x-coordinate is [`MinerIdentity::xonly`], and each bead key has
    /// exactly one `PeerId`. BIP340 signing is unaffected (it normalises internally).
    ///
    /// # Errors
    /// If libp2p rejects the secret bytes, which cannot happen for a valid `SecretKey`.
    pub fn libp2p_keypair(
        &self,
    ) -> Result<libp2p::identity::Keypair, libp2p::identity::DecodingError> {
        let canonical = canonical_secret(&self.secret);
        // `try_from_bytes` zeroizes its input on success; clear our copy on failure too.
        let mut bytes = canonical.secret_bytes();
        let secret = match libp2p::identity::secp256k1::SecretKey::try_from_bytes(&mut bytes) {
            Ok(secret) => secret,
            Err(e) => {
                bytes.fill(0);
                return Err(e);
            }
        };
        Ok(libp2p::identity::secp256k1::Keypair::from(secret).into())
    }
}

/// The even-y form of `secret`: `secret` itself if its public point has an even y, else its
/// negation `n - secret`.
///
/// A secret and its negation share one x-only key, so anything that must agree on one point
/// (the libp2p key) uses this form and never has to guess a parity.
pub fn canonical_secret(secret: &SecretKey) -> SecretKey {
    let secp = Secp256k1::new();
    let (_, parity) =
        bitcoin::secp256k1::Keypair::from_secret_key(&secp, secret).x_only_public_key();
    match parity {
        bitcoin::secp256k1::Parity::Even => *secret,
        bitcoin::secp256k1::Parity::Odd => secret.negate(),
    }
}

/// Multihash code of the identity hash function: the digest is the data itself.
const IDENTITY_MULTIHASH_CODE: u64 = 0x00;

/// The BIP340 x-only key of a libp2p public key, if it is a canonical secp256k1 key.
///
/// Only the even-y form (`02` prefix) counts: that is what [`MinerIdentity::libp2p_keypair`]
/// produces. The odd-y form of the same x-only key (`03`) and every other key type give `None`.
pub fn xonly_from_public_key(public_key: &libp2p::identity::PublicKey) -> Option<XOnlyPublicKey> {
    let compressed = public_key.clone().try_into_secp256k1().ok()?.to_bytes();
    if compressed[0] != 0x02 {
        return None;
    }
    XOnlyPublicKey::from_slice(&compressed[1..33]).ok()
}

/// The BIP340 x-only key embedded in a secp256k1 `PeerId`.
pub fn xonly_from_peer_id(peer_id: &libp2p::PeerId) -> Option<XOnlyPublicKey> {
    let multihash = peer_id.as_ref();
    if multihash.code() != IDENTITY_MULTIHASH_CODE {
        return None;
    }
    let public_key = libp2p::identity::PublicKey::try_decode_protobuf(multihash.digest()).ok()?;
    xonly_from_public_key(&public_key)
}

/// True if `peer_id` is a secp256k1 identity whose x-coordinate equals `comm_pub_key`.
pub fn peer_id_matches_xonly(peer_id: &libp2p::PeerId, comm_pub_key: &XOnlyPublicKey) -> bool {
    xonly_from_peer_id(peer_id).is_some_and(|x| x == *comm_pub_key)
}

fn miner_key_path(datadir: &Path) -> PathBuf {
    datadir.join(MINER_SECP256K1_FILENAME)
}

#[cfg(test)]
mod tests {
    use super::*;
    use libp2p::identity::Keypair;
    use std::fs;
    use std::sync::atomic::{AtomicU64, Ordering};
    use std::time::{SystemTime, UNIX_EPOCH};

    fn unique_dir() -> PathBuf {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!(
            "braidpool-miner-id-{}-{nanos}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[test]
    fn two_generated_identities_differ() {
        let a = MinerIdentity::generate();
        let b = MinerIdentity::generate();
        assert_ne!(a.xonly(), b.xonly());
    }

    #[test]
    fn test_fixture_is_stable() {
        assert_eq!(
            MinerIdentity::test_fixture().xonly(),
            MinerIdentity::test_fixture().xonly()
        );
    }

    #[test]
    fn debug_omits_secret() {
        let identity = MinerIdentity::test_fixture();
        let debug = format!("{:?}", identity);
        assert!(debug.contains("xonly"));
        assert!(!debug.contains("secret"));
        assert!(!debug.contains(&hex::encode(identity.secret_for_tests().secret_bytes())));
    }

    #[test]
    fn load_or_generate_is_stable() {
        let dir = unique_dir();
        let first = MinerIdentity::load_or_generate(&dir).unwrap();
        let second = MinerIdentity::load_or_generate(&dir).unwrap();
        assert_eq!(first.xonly(), second.xonly());
        let _ = fs::remove_dir_all(&dir);
    }

    #[cfg(unix)]
    #[test]
    fn generated_key_file_is_owner_read_only_and_32_bytes() {
        use std::os::unix::fs::PermissionsExt;
        let dir = unique_dir();
        MinerIdentity::load_or_generate(&dir).unwrap();
        let path = dir.join(MINER_SECP256K1_FILENAME);
        assert_eq!(
            fs::metadata(&path).unwrap().permissions().mode() & 0o777,
            0o400
        );
        assert_eq!(fs::read(&path).unwrap().len(), 32);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn wrong_length_file_is_an_error_and_is_not_replaced() {
        let dir = unique_dir();
        let path = dir.join(MINER_SECP256K1_FILENAME);
        fs::write(&path, [1u8; 31]).unwrap();
        let err = MinerIdentity::load_or_generate(&dir).unwrap_err();
        assert_eq!(err.kind(), ErrorKind::InvalidData);
        assert_eq!(fs::read(&path).unwrap(), vec![1u8; 31]);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn zero_scalar_is_an_error_and_is_not_replaced() {
        let dir = unique_dir();
        let path = dir.join(MINER_SECP256K1_FILENAME);
        fs::write(&path, [0u8; 32]).unwrap();
        let err = MinerIdentity::load_or_generate(&dir).unwrap_err();
        assert_eq!(err.kind(), ErrorKind::InvalidData);
        assert_eq!(fs::read(&path).unwrap(), vec![0u8; 32]);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn unreadable_key_path_is_an_error_not_a_new_identity() {
        let dir = unique_dir();
        let path = dir.join(MINER_SECP256K1_FILENAME);
        fs::create_dir(&path).unwrap();
        assert!(MinerIdentity::load_or_generate(&dir).is_err());
        assert!(path.is_dir());
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn concurrent_first_start_yields_one_identity() {
        use std::sync::{Arc, Barrier};
        let dir = Arc::new(unique_dir());
        let barrier = Arc::new(Barrier::new(8));
        let handles: Vec<_> = (0..8)
            .map(|_| {
                let (dir, barrier) = (Arc::clone(&dir), Arc::clone(&barrier));
                std::thread::spawn(move || {
                    barrier.wait();
                    MinerIdentity::load_or_generate(&*dir).unwrap().xonly()
                })
            })
            .collect();
        let keys: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
        assert!(keys.iter().all(|k| *k == keys[0]));
        assert_eq!(
            MinerIdentity::load_or_generate(&*dir).unwrap().xonly(),
            keys[0]
        );
        let _ = fs::remove_dir_all(&*dir);
    }

    #[test]
    fn peer_id_of_derived_key_carries_the_bead_key() {
        let identity = MinerIdentity::generate();
        let peer_id = identity.libp2p_keypair().unwrap().public().to_peer_id();
        assert_eq!(xonly_from_peer_id(&peer_id), Some(identity.xonly()));
        assert!(peer_id_matches_xonly(&peer_id, &identity.xonly()));
    }

    #[test]
    fn derived_libp2p_key_is_always_the_even_y_form() {
        // A bead key must map to one PeerId: whatever the parity of the secret's public point,
        // the derived libp2p key is the 02 form, and its x is the bead key.
        let (mut even_secrets, mut odd_secrets) = (0, 0);
        for _ in 0..64 {
            let identity = MinerIdentity::generate();
            let secp = bitcoin::secp256k1::Secp256k1::new();
            let (_, parity) =
                bitcoin::secp256k1::Keypair::from_secret_key(&secp, identity.secret_for_tests())
                    .x_only_public_key();
            match parity {
                bitcoin::secp256k1::Parity::Even => even_secrets += 1,
                bitcoin::secp256k1::Parity::Odd => odd_secrets += 1,
            }
            let public = identity.libp2p_keypair().unwrap().public();
            let compressed = public.clone().try_into_secp256k1().unwrap().to_bytes();
            assert_eq!(compressed[0], 0x02);
            assert_eq!(xonly_from_public_key(&public), Some(identity.xonly()));
            assert!(peer_id_matches_xonly(
                &public.to_peer_id(),
                &identity.xonly()
            ));
        }
        assert!(
            even_secrets > 0 && odd_secrets > 0,
            "64 secrets should include both parities"
        );
    }

    #[test]
    fn a_secret_and_its_negation_are_one_peer() {
        let identity = MinerIdentity::generate();
        let negated = MinerIdentity::from_secret(identity.secret_for_tests().negate());
        assert_eq!(identity.xonly(), negated.xonly());
        assert_eq!(
            identity.libp2p_keypair().unwrap().public().to_peer_id(),
            negated.libp2p_keypair().unwrap().public().to_peer_id()
        );
    }

    #[test]
    fn odd_y_libp2p_key_is_not_a_miner_identity() {
        // Someone who builds the 03 form by hand (the un-normalised secret) gets a PeerId whose
        // x equals a bead key, but it is not the canonical one and carries no miner key.
        let identity = MinerIdentity::generate();
        let canonical_keypair = identity.libp2p_keypair().unwrap();
        let canonical = canonical_keypair.public();
        // The canonical secret has an even-y public point; its negation has the odd-y one.
        let canonical_secret = canonical_keypair
            .try_into_secp256k1()
            .unwrap()
            .secret()
            .to_bytes();
        let mut odd_bytes = bitcoin::secp256k1::SecretKey::from_slice(&canonical_secret)
            .unwrap()
            .negate()
            .secret_bytes();
        let odd_secret =
            libp2p::identity::secp256k1::SecretKey::try_from_bytes(&mut odd_bytes).unwrap();
        let odd =
            libp2p::identity::Keypair::from(libp2p::identity::secp256k1::Keypair::from(odd_secret))
                .public();
        let odd_compressed = odd.clone().try_into_secp256k1().unwrap().to_bytes();
        assert_eq!(odd_compressed[0], 0x03);
        assert_eq!(
            odd.clone().try_into_secp256k1().unwrap().to_bytes()[1..],
            canonical.clone().try_into_secp256k1().unwrap().to_bytes()[1..]
        );
        assert_ne!(odd.to_peer_id(), canonical.to_peer_id());
        assert_eq!(xonly_from_public_key(&odd), None);
        assert_eq!(xonly_from_peer_id(&odd.to_peer_id()), None);
    }

    #[test]
    fn different_miner_does_not_match() {
        let a = MinerIdentity::generate();
        let b = MinerIdentity::generate();
        let peer_a = a.libp2p_keypair().unwrap().public().to_peer_id();
        assert!(!peer_id_matches_xonly(&peer_a, &b.xonly()));
    }

    #[test]
    fn ed25519_peer_id_has_no_miner_key() {
        let ed = Keypair::generate_ed25519();
        assert!(xonly_from_public_key(&ed.public()).is_none());
        assert!(xonly_from_peer_id(&ed.public().to_peer_id()).is_none());
    }

    #[test]
    fn same_secret_gives_the_same_peer_id() {
        let secret = bitcoin::secp256k1::SecretKey::from_slice(&[0x11u8; 32]).unwrap();
        let a = MinerIdentity::from_secret(secret).libp2p_keypair().unwrap();
        let b = MinerIdentity::from_secret(secret).libp2p_keypair().unwrap();
        assert_eq!(a.public().to_peer_id(), b.public().to_peer_id());
    }

    #[test]
    fn bead_verifies_under_the_key_read_from_the_signers_peer_id() {
        use crate::bead::sign::verify_uncommitted_signature;
        use crate::utils::create_test_bead;
        let identity = MinerIdentity::generate();
        let peer_id = identity.libp2p_keypair().unwrap().public().to_peer_id();

        let mut bead = create_test_bead(1, None);
        identity.sign_bead(&mut bead).unwrap();
        verify_uncommitted_signature(&bead).unwrap();

        // The key a peer reads out of the PeerId is the key the bead is signed under.
        let from_peer = xonly_from_peer_id(&peer_id).unwrap();
        assert_eq!(from_peer, bead.committed_metadata.comm_pub_key);
        assert!(peer_id_matches_xonly(
            &peer_id,
            &bead.committed_metadata.comm_pub_key
        ));
    }

    #[test]
    fn canonical_secret_is_idempotent_and_even_y() {
        let secp = bitcoin::secp256k1::Secp256k1::new();
        for _ in 0..64 {
            let sk = *MinerIdentity::generate().secret_for_tests();
            let canonical = canonical_secret(&sk);
            assert_eq!(canonical_secret(&canonical), canonical);
            let (_, parity) =
                bitcoin::secp256k1::Keypair::from_secret_key(&secp, &canonical).x_only_public_key();
            assert_eq!(parity, bitcoin::secp256k1::Parity::Even);
        }
    }
}
