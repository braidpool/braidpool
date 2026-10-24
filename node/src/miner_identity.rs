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
use std::collections::HashSet;
use std::fmt;
use std::io::{self, ErrorKind};
use std::path::{Path, PathBuf};
use std::sync::OnceLock;
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

    /// Refuse to run with a denied key: anyone who knows its secret could sign as this node.
    ///
    /// # Errors
    /// `InvalidData` naming the key if it is on `denylist`.
    pub fn ensure_allowed(&self, denylist: &KeyDenylist) -> io::Result<()> {
        if denylist.contains(&self.xonly) {
            return Err(io::Error::new(
                ErrorKind::InvalidData,
                format!(
                    "miner key {} is on the key denylist; delete the {MINER_SECP256K1_FILENAME} \
                     file to generate a new one",
                    self.xonly
                ),
            ));
        }
        Ok(())
    }
}

/// Secrets `1..=KNOWN_SMALL_SECRETS` are public by construction: anyone can compute `k * G`.
pub const KNOWN_SMALL_SECRETS: u32 = 1024;

/// Secret keys published with the BIP340 test vectors 1 to 3. Vector 0 (secret 3) is already
/// one of the small secrets.
const BIP340_TEST_VECTOR_SECRETS: [&str; 3] = [
    "B7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFEF",
    "C90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B14E5C9",
    "0B432B2677937381AEF05BB02A66ECD012773062CF3FA2549E44F58ED2401710",
];

/// Miner keys that are never accepted because their secrets are publicly known.
///
/// A validation policy, not part of the encoding: changing the list never changes the wire
/// format. The default list is computed from secrets, so a secret and its negation (which share
/// one x-only key) are both covered.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct KeyDenylist {
    keys: HashSet<XOnlyPublicKey>,
}

impl KeyDenylist {
    /// A list that denies nothing.
    pub fn empty() -> Self {
        Self::default()
    }

    /// The built-in list: the keys of the secrets `1..=KNOWN_SMALL_SECRETS` (including the
    /// generator point, secret 1) and of the BIP340 test-vector secrets.
    pub fn known_secrets() -> Self {
        let mut list = Self::empty();
        for k in 1..=KNOWN_SMALL_SECRETS {
            let mut bytes = [0u8; 32];
            bytes[28..].copy_from_slice(&k.to_be_bytes());
            if let Ok(secret) = SecretKey::from_slice(&bytes) {
                list.keys.insert(MinerIdentity::from_secret(secret).xonly());
            }
        }
        for hex in BIP340_TEST_VECTOR_SECRETS {
            if let Some(secret) = hex::decode(hex)
                .ok()
                .and_then(|bytes| SecretKey::from_slice(&bytes).ok())
            {
                list.keys.insert(MinerIdentity::from_secret(secret).xonly());
            }
        }
        list
    }

    /// Build the list from the node's flags: the built-in list unless `no_default`, plus each
    /// `extra` key.
    ///
    /// # Errors
    /// A message naming the first `extra` entry that is not a 64-hex-character x-only key.
    pub fn from_flags(no_default: bool, extra: &[String]) -> Result<Self, String> {
        let mut list = if no_default {
            Self::empty()
        } else {
            Self::known_secrets()
        };
        for entry in extra {
            let bytes = hex::decode(entry.trim())
                .map_err(|e| format!("--deny-key {entry}: not hex: {e}"))?;
            let key = crate::bead::sign::parse_xonly_pubkey(&bytes)
                .map_err(|e| format!("--deny-key {entry}: {e}"))?;
            list = list.with_key(key);
        }
        Ok(list)
    }

    /// This list plus one more denied key.
    pub fn with_key(mut self, key: XOnlyPublicKey) -> Self {
        self.keys.insert(key);
        self
    }

    /// True if `key` is denied.
    pub fn contains(&self, key: &XOnlyPublicKey) -> bool {
        self.keys.contains(key)
    }

    /// Number of denied keys.
    pub fn len(&self) -> usize {
        self.keys.len()
    }

    /// True if the list denies nothing.
    pub fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }
}

static ACTIVE_KEY_DENYLIST: OnceLock<KeyDenylist> = OnceLock::new();

/// Install the denylist this process enforces. Call once at startup, before any bead is
/// verified.
///
/// # Errors
/// Returns `list` back if a denylist is already installed or was already read.
pub fn set_active_key_denylist(list: KeyDenylist) -> Result<(), KeyDenylist> {
    ACTIVE_KEY_DENYLIST.set(list)
}

/// The denylist this process enforces; empty unless [`set_active_key_denylist`] installed one,
/// so unit tests that sign with secret 1 are unaffected.
pub fn active_key_denylist() -> &'static KeyDenylist {
    ACTIVE_KEY_DENYLIST.get_or_init(KeyDenylist::default)
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

    fn key_of_secret(k: u32) -> XOnlyPublicKey {
        let mut bytes = [0u8; 32];
        bytes[28..].copy_from_slice(&k.to_be_bytes());
        MinerIdentity::from_secret(SecretKey::from_slice(&bytes).unwrap()).xonly()
    }

    #[test]
    fn default_denylist_covers_the_known_secret_groups() {
        let list = KeyDenylist::known_secrets();
        for hex in [
            "79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798",
            "c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5",
            "f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9",
        ] {
            assert!(list.contains(&hex.parse().unwrap()), "{hex}");
        }
        assert!(list.contains(&key_of_secret(KNOWN_SMALL_SECRETS)));
        assert!(!list.contains(&key_of_secret(KNOWN_SMALL_SECRETS + 1)));
        // Public keys as published with BIP340 test vectors 1 to 3.
        for hex in [
            "dff1d77f2a671c5f36183726db2341be58feae1da2deced843240f7b502ba659",
            "dd308afec5777e13121fa72b9cc1b7cc0139715309b086c960e18fd969774eb8",
            "25d1dff95105f5253c4022f628a996ad3a0d95fbf21d468a1b33f8c160d8f517",
        ] {
            assert!(list.contains(&hex.parse().unwrap()), "{hex}");
        }
        assert_eq!(list.len(), KNOWN_SMALL_SECRETS as usize + 3);
    }

    #[test]
    fn denylist_does_not_touch_ordinary_keys() {
        let list = KeyDenylist::known_secrets();
        for _ in 0..64 {
            assert!(!list.contains(&MinerIdentity::generate().xonly()));
        }
        assert!(KeyDenylist::empty().is_empty());
    }

    #[test]
    fn negated_secret_of_a_denied_key_is_denied_too() {
        let mut one = [0u8; 32];
        one[31] = 1;
        let negated = SecretKey::from_slice(&one).unwrap().negate();
        assert!(KeyDenylist::known_secrets().contains(&MinerIdentity::from_secret(negated).xonly()));
    }

    #[test]
    fn from_flags_combines_the_default_list_and_extra_keys() {
        let extra = MinerIdentity::generate().xonly();
        let list = KeyDenylist::from_flags(false, &[format!(" {extra}\n")]).unwrap();
        assert!(list.contains(&extra));
        assert!(list.contains(&key_of_secret(1)));
        assert_eq!(list.len(), KNOWN_SMALL_SECRETS as usize + 4);

        let only_extra = KeyDenylist::from_flags(true, &[extra.to_string()]).unwrap();
        assert_eq!(only_extra.len(), 1);
        assert!(!only_extra.contains(&key_of_secret(1)));
        assert!(KeyDenylist::from_flags(true, &[]).unwrap().is_empty());
    }

    #[test]
    fn from_flags_rejects_keys_that_are_not_x_only() {
        let compressed = format!("02{}", key_of_secret(5000));
        let not_on_curve = "00".repeat(32);
        for bad in ["zz", "79be667e", compressed.as_str(), not_on_curve.as_str()] {
            let err = KeyDenylist::from_flags(false, &[bad.to_string()]).unwrap_err();
            assert!(err.starts_with("--deny-key"), "{bad}: {err}");
        }
    }

    #[test]
    fn ensure_allowed_refuses_a_denied_key_only() {
        let list = KeyDenylist::known_secrets();
        let err = MinerIdentity::test_fixture()
            .ensure_allowed(&list)
            .unwrap_err();
        assert_eq!(err.kind(), ErrorKind::InvalidData);
        assert!(err.to_string().contains(MINER_SECP256K1_FILENAME));
        MinerIdentity::generate().ensure_allowed(&list).unwrap();
        MinerIdentity::test_fixture()
            .ensure_allowed(&KeyDenylist::empty())
            .unwrap();
    }
}
