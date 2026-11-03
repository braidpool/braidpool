//! Per-node secp256k1 miner identity used for BIP340 bead signatures.
//!
//! The secret is stored at `datadir/miner_secp256k1` (see [`crate::secret_file`]). It is
//! separate from the libp2p `keystore`.

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
}

fn miner_key_path(datadir: &Path) -> PathBuf {
    datadir.join(MINER_SECP256K1_FILENAME)
}

#[cfg(test)]
mod tests {
    use super::*;
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
}
