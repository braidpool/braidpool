//! Per-node secp256k1 miner identity used for BIP340 bead signatures.
//!
//! Distinct from the libp2p swarm keystore (ed25519). Both live in the data
//! directory and identify the same process.

use crate::bead::sign::{sign_uncommitted_metadata, BeadSignError};
use crate::bead::Bead;
use bitcoin::secp256k1::{Secp256k1, SecretKey};
use bitcoin::XOnlyPublicKey;
use rand::rngs::OsRng;
use std::fs;
use std::io::{self, ErrorKind};
use std::path::{Path, PathBuf};
use tracing::{info, warn};

/// File name of the secp256k1 miner secret next to the libp2p `keystore`.
pub const MINER_SECP256K1_FILENAME: &str = "miner_secp256k1";

/// secp256k1 key used as `CommittedMetadata.comm_pub_key` and to Schnorr-sign
/// uncommitted metadata.
#[derive(Clone, Debug)]
pub struct MinerIdentity {
    secret: SecretKey,
    xonly: XOnlyPublicKey,
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
        let xonly = XOnlyPublicKey::from_slice(&xonly.serialize())
            .expect("keypair x-only serialize is valid");
        Self { secret, xonly }
    }

    /// Load `datadir/miner_secp256k1` or generate and persist a new 32-byte secret.
    pub fn load_or_generate(datadir: impl AsRef<Path>) -> io::Result<Self> {
        let path = miner_key_path(datadir.as_ref());
        match fs::read(&path) {
            Ok(bytes) => {
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
                        format!("invalid miner secp256k1 secret: {e}"),
                    )
                })?;
                info!(path = %path.display(), "Loaded miner secp256k1 identity");
                Ok(Self::from_secret(secret))
            }
            Err(e) if e.kind() == ErrorKind::NotFound => {
                let identity = Self::generate();
                fs::write(&path, identity.secret.secret_bytes())?;
                #[cfg(unix)]
                {
                    use std::os::unix::fs::PermissionsExt;
                    let mut perms = fs::metadata(&path)?.permissions();
                    if perms.mode() & 0o777 != 0o400 {
                        warn!(
                            path = %path.display(),
                            permissions = perms.mode() & 0o777,
                            "Miner key permissions are not 0o400; setting them"
                        );
                        perms.set_mode(0o400);
                        fs::set_permissions(&path, perms)?;
                    }
                }
                info!(path = %path.display(), "Generated miner secp256k1 identity");
                Ok(identity)
            }
            Err(e) => Err(e),
        }
    }

    /// X-only public key committed in every bead this node forms.
    pub fn xonly(&self) -> XOnlyPublicKey {
        self.xonly
    }

    /// Secret key used to Schnorr-sign uncommitted metadata.
    pub fn secret(&self) -> &SecretKey {
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
    use std::time::{SystemTime, UNIX_EPOCH};

    fn unique_dir() -> PathBuf {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let dir = std::env::temp_dir().join(format!(
            "braidpool-miner-id-{}-{}",
            std::process::id(),
            nanos
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
    fn load_or_generate_is_stable() {
        let dir = unique_dir();
        let first = MinerIdentity::load_or_generate(&dir).unwrap();
        let second = MinerIdentity::load_or_generate(&dir).unwrap();
        assert_eq!(first.xonly(), second.xonly());
        let _ = fs::remove_dir_all(&dir);
    }
}
