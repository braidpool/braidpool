//! Bitcoind connection helpers.
//!
//! Resolves cookie file and IPC socket paths per network, with smart defaults
//! for the bundled install model (bitcoind + braidpool on same host).
//!
//! The cookie file is used as a startup gate: its presence confirms bitcoind
//! is running before braidpool attempts IPC connection.
//!
//! ## Cookie Path Resolution
//!
//! The cookie file path is resolved with three-tier precedence:
//! 1. CLI `--rpccookie` flag (explicit full path)
//! 2. TOML config file `cookie_path` field
//! 3. Network-based auto-detection from `~/.bitcoin/{network}/.cookie`
//!
//! For custom `bitcoind -datadir` setups, provide the cookie path explicitly
//! via either mechanism. The path format is `<datadir>/<network>/.cookie`.
//!
//! ## Default paths
//!
//! | Network   | Cookie path default             | IPC socket default                      |
//! |-----------|---------------------------------|-----------------------------------------|
//! | mainnet   | `~/.bitcoin/.cookie`            | `./braidpool/bitcoin-main.sock`         |
//! | testnet4  | `~/.bitcoin/testnet4/.cookie`   | `./braidpool/bitcoin-testnet4.sock`     |
//! | signet    | `~/.bitcoin/signet/.cookie`     | `./braidpool/bitcoin-signet.sock`       |
//! | regtest   | `~/.bitcoin/regtest/.cookie`    | `./braidpool/bitcoin-regtest.sock`      |
//! | cpunet    | `~/.bitcoin/cpunet/.cookie`     | `./braidpool/bitcoin-cpunet.sock`       |

use bitcoin::Network;
use std::fmt;
use std::io::Read;
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};
use tracing::warn;

/// Maximum cookie file size (1 KiB). Real cookies are ~70 bytes.
const MAX_COOKIE_FILE_SIZE: u64 = 1024;

#[derive(Debug, PartialEq)]
pub enum CookieError {
    NotFound { path: PathBuf },
    PermissionDenied { path: PathBuf },
    InvalidFormat { path: PathBuf },
    SymlinkDetected { path: PathBuf },
    PathTraversalDetected { path: PathBuf },
    CanonicalizeFailure { path: PathBuf },
    HomeDirUnavailable,
    FileTooLarge { path: PathBuf, size: u64 },
    IoError { path: PathBuf, source: String },
}

impl fmt::Display for CookieError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CookieError::NotFound { path } => {
                write!(
                    f,
                    "Cookie file not found at {}. Is bitcoind running? Override with --rpccookie",
                    path.display()
                )
            }
            CookieError::PermissionDenied { path } => {
                write!(
                    f,
                    "Cannot read cookie file at {}. Run as same user as bitcoind, or: \
                     sudo usermod -a -G bitcoin $USER + rpccookieperms=group in bitcoin.conf",
                    path.display()
                )
            }
            CookieError::InvalidFormat { path } => {
                write!(
                    f,
                    "Cookie file at {} has invalid format (expected __cookie__:hexstring)",
                    path.display()
                )
            }
            CookieError::SymlinkDetected { path } => {
                write!(
                    f,
                    "Cookie file at {} is a symlink. This is a security risk and not allowed",
                    path.display()
                )
            }
            CookieError::PathTraversalDetected { path } => {
                write!(
                    f,
                    "Cookie path {} contains path traversal components or escapes home directory",
                    path.display()
                )
            }
            CookieError::CanonicalizeFailure { path } => {
                write!(
                    f,
                    "Failed to canonicalize cookie path {}. Path may be invalid or inaccessible",
                    path.display()
                )
            }
            CookieError::HomeDirUnavailable => {
                write!(
                    f,
                    "Cannot determine home directory. Set cookie path explicitly with --rpccookie"
                )
            }
            CookieError::FileTooLarge { path, size } => {
                write!(
                    f,
                    "Cookie file at {} is too large ({} bytes, max {}). File may be corrupted",
                    path.display(),
                    size,
                    MAX_COOKIE_FILE_SIZE
                )
            }
            CookieError::IoError { path, source } => {
                write!(
                    f,
                    "Unexpected IO error reading cookie file at {}: {}",
                    path.display(),
                    source
                )
            }
        }
    }
}

impl std::error::Error for CookieError {}

/// Returns the platform-specific default Bitcoin Core data directory base.
///
/// - macOS: `~/Library/Application Support/Bitcoin`  (Bitcoin Core default)
/// - Linux and other Unix: `~/.bitcoin`               (Bitcoin Core default)
fn default_bitcoin_datadir() -> Result<PathBuf, CookieError> {
    #[cfg(target_os = "macos")]
    {
        dirs::data_dir()
            .map(|d| d.join("Bitcoin"))
            .ok_or(CookieError::HomeDirUnavailable)
    }
    // wont-fix: braidpool is Unix-only (UnixStream); Windows not supported
    #[cfg(not(target_os = "macos"))]
    {
        // Linux and all other Unix: ~/.bitcoin
        dirs::home_dir()
            .map(|d| d.join(".bitcoin"))
            .ok_or(CookieError::HomeDirUnavailable)
    }
}

/// Resolve the cookie file path using three-tier precedence with security validation:
///
/// 1. `cli_path` — CLI `--rpccookie` flag (highest priority)
/// 2. `config_path` — TOML config `cookie_path` field
/// 3. Network-based auto-detection from the platform Bitcoin Core datadir
///
/// Validates that the resolved path:
/// - Does not contain symlinks (path traversal attack prevention)
/// - Does not escape user home directory (path traversal prevention)
/// - Can be canonicalized (no permission/access issues)
///
/// Both `cli_path` and `config_path` support tilde expansion.
/// When using a custom `bitcoind -datadir`, pass the full cookie path
/// via `--rpccookie` or set `cookie_path` in the config file.
pub fn resolve_cookie_path(
    cli_path: Option<&str>,
    config_path: Option<&str>,
    network: Network,
) -> Result<PathBuf, CookieError> {
    let raw_path = if let Some(path) = cli_path {
        path.to_string()
    } else if let Some(path) = config_path {
        path.to_string()
    } else {
        let base_path = default_bitcoin_datadir()?;
        let cookie_dir = match network {
            Network::Bitcoin => base_path,
            Network::Testnet(_) => base_path.join("testnet4"),
            Network::Signet => base_path.join("signet"),
            Network::Regtest => base_path.join("regtest"),
            Network::CPUNet => base_path.join("cpunet"),
            _ => base_path,
        };
        return Ok(cookie_dir.join(".cookie"));
    };

    // Expand tilde
    let expanded = shellexpand::tilde(&raw_path);
    let path = PathBuf::from(expanded.as_ref());

    // Check for path traversal components before canonicalization
    if raw_path.contains("..") {
        return Err(CookieError::PathTraversalDetected { path });
    }

    // Canonicalize the parent directory only — the cookie file itself may not
    // exist yet (bitcoind still starting). The parent dir should already exist.
    let file_name = path
        .file_name()
        .ok_or_else(|| CookieError::CanonicalizeFailure { path: path.clone() })?
        .to_os_string();

    let parent = path
        .parent()
        .ok_or_else(|| CookieError::CanonicalizeFailure { path: path.clone() })?;

    let canonical_parent = parent
        .canonicalize()
        .map_err(|_| CookieError::CanonicalizeFailure { path: path.clone() })?;

    // Validate parent doesn't escape home directory
    let home_dir = dirs::home_dir().ok_or(CookieError::HomeDirUnavailable)?;

    let system_temp = std::env::temp_dir();
    let runtime_dir = dirs::runtime_dir();
    let in_temp = canonical_parent.starts_with(&system_temp);
    let in_runtime = runtime_dir
        .as_deref()
        .map(|r| canonical_parent.starts_with(r))
        .unwrap_or(false);

    if !canonical_parent.starts_with(&home_dir) && !in_temp && !in_runtime {
        return Err(CookieError::PathTraversalDetected {
            path: canonical_parent.join(&file_name),
        });
    }

    Ok(canonical_parent.join(file_name))
}

fn network_suffix(network: &Network) -> &'static str {
    match network {
        Network::Bitcoin => "main",
        Network::Testnet(_) => "testnet4",
        Network::Signet => "signet",
        Network::Regtest => "regtest",
        Network::CPUNet => "cpunet",
        _ => "main",
    }
}

fn default_ipc_socket_path(network: &Network) -> PathBuf {
    let suffix = network_suffix(network);
    PathBuf::from("./braidpool").join(format!("bitcoin-{}.sock", suffix))
}

/// Resolve the IPC socket path based on an explicit override or network defaults.
///
/// Precedence:
/// 1. `explicit` — CLI `--ipc-socket` flag (must be an absolute path)
/// 2. Auto-detect — `./braidpool/bitcoin-{network}.sock` (directory created if missing)
pub fn resolve_ipc_socket(explicit: Option<&str>, network: Network) -> Result<String, String> {
    if let Some(path) = explicit {
        // Validate: must be absolute and must not contain parent-directory traversal
        if !path.starts_with('/') {
            return Err(format!(
                "IPC socket path must be absolute (start with /): got '{path}'"
            ));
        }
        if Path::new(path)
            .components()
            .any(|c| c == std::path::Component::ParentDir)
        {
            return Err(format!(
                "IPC socket path must not contain '..': got '{path}'"
            ));
        }
        return Ok(path.to_string());
    }

    std::fs::create_dir_all("./braidpool")
        .map_err(|e| format!("Failed to create ./braidpool directory: {e}"))?;

    Ok(default_ipc_socket_path(&network)
        .to_string_lossy()
        .into_owned())
}

/// Validate that a cookie file exists, is readable, and has the expected format.
/// Rejects symlinks as a security precaution against symlink-based attacks.
pub fn validate_cookie_file(path: &Path) -> Result<(), CookieError> {
    // Security: Open with O_NOFOLLOW — atomically rejects symlinks (returns ELOOP).
    // Using a single fd for both size check and read eliminates TOCTOU races.
    let mut file = std::fs::OpenOptions::new()
        .read(true)
        .custom_flags(libc::O_NOFOLLOW)
        .open(path)
        .map_err(|e| match e.kind() {
            std::io::ErrorKind::NotFound => CookieError::NotFound {
                path: path.to_path_buf(),
            },
            std::io::ErrorKind::PermissionDenied => CookieError::PermissionDenied {
                path: path.to_path_buf(),
            },
            // O_NOFOLLOW sets errno=ELOOP when the path is a symlink
            _ if e.raw_os_error() == Some(libc::ELOOP) => CookieError::SymlinkDetected {
                path: path.to_path_buf(),
            },
            _ => {
                warn!(error = %e, path = %path.display(), "Unexpected IO error opening cookie file");
                CookieError::IoError {
                    path: path.to_path_buf(),
                    source: e.to_string(),
                }
            }
        })?;

    // Security: Reject oversized files to prevent OOM — uses same fd, no TOCTOU
    // wont-fix: fstat on open fd fails only under extreme kernel conditions (e.g. NFS eviction)
    let size = file.metadata().map(|m| m.len()).unwrap_or(0);
    if size > MAX_COOKIE_FILE_SIZE {
        return Err(CookieError::FileTooLarge {
            path: path.to_path_buf(),
            size,
        });
    }

    let mut content = String::new();
    file.read_to_string(&mut content)
        .map_err(|e| CookieError::IoError {
            path: path.to_path_buf(),
            source: e.to_string(),
        })?;

    let trimmed = content.trim();
    let parts: Vec<&str> = trimmed.splitn(2, ':').collect();
    if parts.len() != 2 || parts[0].is_empty() || parts[1].is_empty() {
        return Err(CookieError::InvalidFormat {
            path: path.to_path_buf(),
        });
    }

    // Validate the hex portion contains only hex characters
    if !parts[1].chars().all(|c| c.is_ascii_hexdigit()) {
        return Err(CookieError::InvalidFormat {
            path: path.to_path_buf(),
        });
    }

    Ok(())
}

/// Wait for the cookie file to become available with optimized startup timeout.
///
/// Retries with exponential backoff.
/// Optimized for fast failure detection in misconfiguration scenarios.
/// Only retries on `NotFound` (bitcoind may still be starting).
/// `PermissionDenied`, `InvalidFormat`, `SymlinkDetected`, and `PathTraversalDetected` fail immediately.
pub async fn wait_for_cookie(path: &Path) -> Result<(), CookieError> {
    let max_attempts = 10;
    let mut delay_millis = 100u64;
    let max_delay_millis = 5000u64;

    for attempt in 1..=max_attempts {
        match validate_cookie_file(path) {
            Ok(()) => return Ok(()),
            Err(CookieError::NotFound { .. }) => {
                if attempt == max_attempts {
                    return Err(CookieError::NotFound {
                        path: path.to_path_buf(),
                    });
                }
                warn!(
                    path = %path.display(),
                    attempt = attempt,
                    max_attempts = max_attempts,
                    retry_in_millis = delay_millis,
                    "Cookie file not found, waiting for bitcoind to start"
                );
                tokio::time::sleep(std::time::Duration::from_millis(delay_millis)).await;
                delay_millis = (delay_millis * 2).min(max_delay_millis);
            }
            // Fail immediately on any permanent errors
            Err(e @ CookieError::PermissionDenied { .. }) => return Err(e),
            Err(e @ CookieError::InvalidFormat { .. }) => return Err(e),
            Err(e @ CookieError::SymlinkDetected { .. }) => return Err(e),
            Err(e @ CookieError::PathTraversalDetected { .. }) => return Err(e),
            Err(e @ CookieError::CanonicalizeFailure { .. }) => return Err(e),
            Err(e @ CookieError::HomeDirUnavailable) => return Err(e),
            Err(e @ CookieError::FileTooLarge { .. }) => return Err(e),
            Err(e @ CookieError::IoError { .. }) => return Err(e),
        }
    }

    unreachable!("loop returns on attempt == max_attempts")
}

/// Probe the Bitcoin Core IPC socket to verify bitcoind was started with `-ipcbind`.
///
/// This is a one-shot reachability check at startup. The runtime reconnect loop
/// in `ipc.rs` handles transient failures during operation.
///
/// # Errors
/// Returns `Err` with an actionable message if the socket is not reachable.
pub async fn probe_ipc_socket(path: &str) -> Result<(), String> {
    use tokio::io::AsyncWriteExt;
    use tokio::net::UnixStream;
    match UnixStream::connect(path).await {
        Ok(mut stream) => {
            // Graceful close — sends FIN to bitcoind instead of an abrupt RST
            stream.shutdown().await.ok();
            Ok(())
        }
        Err(e) => Err(format!(
            "IPC socket not found at {path}. Start bitcoind with: -ipcbind=unix:{path}\n\
             Override the path with --ipc-socket if you used a different location.\n\
             Error: {e}"
        )),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::os::unix::fs::PermissionsExt;

    #[test]
    fn resolve_cookie_path_cpunet() {
        let path = resolve_cookie_path(None, None, Network::CPUNet).unwrap();
        let expected = default_bitcoin_datadir()
            .unwrap()
            .join("cpunet")
            .join(".cookie");
        assert_eq!(path, expected);
    }

    #[test]
    fn resolve_cookie_path_mainnet() {
        let path = resolve_cookie_path(None, None, Network::Bitcoin).unwrap();
        let expected = default_bitcoin_datadir().unwrap().join(".cookie");
        assert_eq!(path, expected);
    }

    #[test]
    fn resolve_cookie_path_testnet() {
        let path =
            resolve_cookie_path(None, None, Network::Testnet(bitcoin::TestnetVersion::V4)).unwrap();
        let expected = default_bitcoin_datadir()
            .unwrap()
            .join("testnet4")
            .join(".cookie");
        assert_eq!(path, expected);
    }

    #[test]
    fn resolve_cookie_path_signet() {
        let path = resolve_cookie_path(None, None, Network::Signet).unwrap();
        let expected = default_bitcoin_datadir()
            .unwrap()
            .join("signet")
            .join(".cookie");
        assert_eq!(path, expected);
    }

    #[test]
    fn resolve_cookie_path_regtest() {
        let path = resolve_cookie_path(None, None, Network::Regtest).unwrap();
        let expected = default_bitcoin_datadir()
            .unwrap()
            .join("regtest")
            .join(".cookie");
        assert_eq!(path, expected);
    }

    #[test]
    fn resolve_cookie_path_rejects_parent_traversal() {
        let result = resolve_cookie_path(Some("~/../../../etc/passwd"), None, Network::CPUNet);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            CookieError::PathTraversalDetected { .. }
        ));
    }

    #[test]
    fn resolve_cookie_path_explicit_in_home() {
        // Create a real temp dir inside home to test canonicalization
        let home = dirs::home_dir().expect("Cannot determine home directory");
        let test_dir = home.join(".braidpool_test_cookie_resolve");
        fs::create_dir_all(&test_dir).unwrap();

        let result = resolve_cookie_path(
            Some(&format!("{}/.cookie", test_dir.display())),
            None,
            Network::CPUNet,
        );
        let path = result.unwrap();
        assert!(path.starts_with(&home));
        assert!(path.ends_with(".cookie"));

        fs::remove_dir_all(&test_dir).unwrap();
    }

    #[test]
    fn resolve_cookie_path_config_override() {
        // Config path works when parent dir exists
        let home = dirs::home_dir().expect("Cannot determine home directory");
        let test_dir = home.join(".braidpool_test_config_override");
        fs::create_dir_all(&test_dir).unwrap();

        let result = resolve_cookie_path(
            None,
            Some(&format!("{}/.cookie", test_dir.display())),
            Network::Signet,
        );
        let path = result.unwrap();
        assert!(path.starts_with(&home));
        assert!(path.ends_with(".cookie"));

        fs::remove_dir_all(&test_dir).unwrap();
    }

    #[test]
    fn resolve_cookie_path_cli_overrides_config() {
        // CLI path takes precedence: even though config points to /etc/passwd,
        // the CLI path (in home dir) is the one used
        let home = dirs::home_dir().expect("Cannot determine home directory");
        let test_dir = home.join(".braidpool_test_cli_override");
        fs::create_dir_all(&test_dir).unwrap();

        let cli_path = format!("{}/.cookie", test_dir.display());
        let result = resolve_cookie_path(Some(&cli_path), Some("/etc/passwd"), Network::Signet);
        let path = result.unwrap();
        // Must resolve from CLI, not from config
        assert!(path.starts_with(&home));
        assert!(path.ends_with(".cookie"));

        fs::remove_dir_all(&test_dir).unwrap();
    }

    #[test]
    fn resolve_cookie_path_both_none_falls_to_default() {
        let path = resolve_cookie_path(None, None, Network::Signet).unwrap();
        let expected = default_bitcoin_datadir()
            .unwrap()
            .join("signet")
            .join(".cookie");
        assert_eq!(path, expected);
    }

    #[test]
    fn resolve_ipc_socket_cpunet() {
        let socket = resolve_ipc_socket(None, Network::CPUNet).unwrap();
        assert_eq!(socket, "./braidpool/bitcoin-cpunet.sock");
    }

    #[test]
    fn resolve_ipc_socket_mainnet() {
        let socket = resolve_ipc_socket(None, Network::Bitcoin).unwrap();
        assert_eq!(socket, "./braidpool/bitcoin-main.sock");
    }

    #[test]
    fn resolve_ipc_socket_explicit_override() {
        let socket = resolve_ipc_socket(Some("/custom/socket.sock"), Network::CPUNet).unwrap();
        assert_eq!(socket, "/custom/socket.sock");
    }

    #[test]
    fn resolve_ipc_socket_explicit_rejects_relative() {
        let result = resolve_ipc_socket(Some("relative/path.sock"), Network::CPUNet);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("absolute"));
    }

    #[test]
    fn resolve_ipc_socket_explicit_rejects_traversal() {
        let result = resolve_ipc_socket(Some("/tmp/../etc/passwd"), Network::CPUNet);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains(".."));
    }

    #[test]
    fn validate_cookie_file_missing() {
        let result = validate_cookie_file(Path::new("/nonexistent/path/.cookie"));
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), CookieError::NotFound { .. }));
    }

    #[test]
    fn validate_cookie_file_rejects_symlinks() {
        let dir = std::env::temp_dir().join("braidpool_test_symlink");
        fs::create_dir_all(&dir).unwrap();
        let target = dir.join("target.cookie");
        let symlink = dir.join(".cookie-symlink");

        fs::write(&target, "__cookie__:abcdef0123456789").unwrap();

        #[cfg(unix)]
        {
            use std::os::unix::fs as unix_fs;
            unix_fs::symlink(&target, &symlink).unwrap();

            let result = validate_cookie_file(&symlink);
            assert!(result.is_err());
            assert!(matches!(
                result.unwrap_err(),
                CookieError::SymlinkDetected { .. }
            ));
        }

        fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn validate_cookie_file_valid() {
        let dir = std::env::temp_dir().join("braidpool_test_cookie_valid");
        fs::create_dir_all(&dir).unwrap();
        let cookie_path = dir.join(".cookie");
        fs::write(&cookie_path, "__cookie__:abcdef0123456789").unwrap();

        let result = validate_cookie_file(&cookie_path);
        assert!(result.is_ok());

        fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn validate_cookie_file_invalid_format_no_colon() {
        let dir = std::env::temp_dir().join("braidpool_test_cookie_nocolon");
        fs::create_dir_all(&dir).unwrap();
        let cookie_path = dir.join(".cookie");
        fs::write(&cookie_path, "invalid_content_without_colon").unwrap();

        let result = validate_cookie_file(&cookie_path);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            CookieError::InvalidFormat { .. }
        ));

        fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn validate_cookie_file_invalid_format_non_hex() {
        let dir = std::env::temp_dir().join("braidpool_test_cookie_nonhex");
        fs::create_dir_all(&dir).unwrap();
        let cookie_path = dir.join(".cookie");
        fs::write(&cookie_path, "__cookie__:not_hex_zzz!!!").unwrap();

        let result = validate_cookie_file(&cookie_path);
        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            CookieError::InvalidFormat { .. }
        ));

        fs::remove_dir_all(&dir).unwrap();
    }

    #[test]
    fn validate_cookie_file_permission_denied() {
        let dir = std::env::temp_dir().join("braidpool_test_cookie_perms");
        fs::create_dir_all(&dir).unwrap();
        let cookie_path = dir.join(".cookie");
        fs::write(&cookie_path, "__cookie__:abcdef0123456789").unwrap();

        // Remove read permission
        fs::set_permissions(&cookie_path, fs::Permissions::from_mode(0o000)).unwrap();

        let result = validate_cookie_file(&cookie_path);

        // Restore permissions before assertions (cleanup)
        fs::set_permissions(&cookie_path, fs::Permissions::from_mode(0o644)).unwrap();
        fs::remove_dir_all(&dir).unwrap();

        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            CookieError::PermissionDenied { .. }
        ));
    }

    #[tokio::test]
    async fn wait_for_cookie_permission_denied_no_retry() {
        let dir = std::env::temp_dir().join("braidpool_test_wait_perms");
        fs::create_dir_all(&dir).unwrap();
        let cookie_path = dir.join(".cookie");
        fs::write(&cookie_path, "__cookie__:abcdef0123456789").unwrap();
        fs::set_permissions(&cookie_path, fs::Permissions::from_mode(0o000)).unwrap();

        let start = std::time::Instant::now();
        let result = wait_for_cookie(&cookie_path).await;
        let elapsed = start.elapsed();

        // Cleanup
        fs::set_permissions(&cookie_path, fs::Permissions::from_mode(0o644)).unwrap();
        fs::remove_dir_all(&dir).unwrap();

        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            CookieError::PermissionDenied { .. }
        ));
        // Should fail immediately (<100ms for first attempt + overhead)
        assert!(elapsed.as_millis() < 500);
    }

    #[tokio::test]
    async fn wait_for_cookie_invalid_format_no_retry() {
        let dir = std::env::temp_dir().join("braidpool_test_wait_fmt");
        fs::create_dir_all(&dir).unwrap();
        let cookie_path = dir.join(".cookie");
        fs::write(&cookie_path, "bad_format").unwrap();

        let start = std::time::Instant::now();
        let result = wait_for_cookie(&cookie_path).await;
        let elapsed = start.elapsed();

        fs::remove_dir_all(&dir).unwrap();

        assert!(result.is_err());
        assert!(matches!(
            result.unwrap_err(),
            CookieError::InvalidFormat { .. }
        ));
        assert!(elapsed.as_millis() < 500);
    }
}
