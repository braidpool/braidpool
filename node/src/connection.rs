use bitcoin::Network;
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use tracing::warn;

#[derive(Debug)]
pub enum CookieError {
    NotFound {
        path: PathBuf,
    },
    PermissionDenied {
        path: PathBuf,
    },
    InvalidFormat {
        path: PathBuf,
    },
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
        }
    }
}

impl std::error::Error for CookieError {}

/// Resolve the cookie file path based on an explicit override or network defaults.
///
/// If `explicit` is `Some`, uses that path (with tilde expansion).
/// Otherwise, returns the default cookie path for the given network.
pub fn resolve_cookie_path(explicit: Option<&str>, network: Network) -> PathBuf {
    if let Some(path) = explicit {
        let expanded = shellexpand::tilde(path);
        return PathBuf::from(expanded.as_ref());
    }

    let base = shellexpand::tilde("~/.bitcoin");
    let base_path = PathBuf::from(base.as_ref());

    let cookie_dir = match network {
        Network::Bitcoin => base_path,
        Network::Testnet(_) => base_path.join("testnet4"),
        Network::Signet => base_path.join("signet"),
        Network::Regtest => base_path.join("regtest"),
        Network::CPUNet => base_path.join("cpunet"),
        _ => base_path,
    };

    cookie_dir.join(".cookie")
}

/// Resolve the IPC socket path based on an explicit override or network defaults.
///
/// If `explicit` is `Some`, uses that path directly.
/// Otherwise, returns the default socket path for the given network.
pub fn resolve_ipc_socket(explicit: Option<&str>, network: Network) -> String {
    if let Some(path) = explicit {
        return path.to_string();
    }

    let suffix = match network {
        Network::Bitcoin => "main",
        Network::Testnet(_) => "testnet4",
        Network::Signet => "signet",
        Network::Regtest => "regtest",
        Network::CPUNet => "cpunet",
        _ => "main",
    };

    format!("/tmp/bitcoin-{}.sock", suffix)
}

/// Validate that a cookie file exists, is readable, and has the expected format.
pub fn validate_cookie_file(path: &Path) -> Result<(), CookieError> {
    let content = match fs::read_to_string(path) {
        Ok(c) => c,
        Err(e) => {
            return match e.kind() {
                std::io::ErrorKind::NotFound => Err(CookieError::NotFound {
                    path: path.to_path_buf(),
                }),
                std::io::ErrorKind::PermissionDenied => Err(CookieError::PermissionDenied {
                    path: path.to_path_buf(),
                }),
                _ => Err(CookieError::NotFound {
                    path: path.to_path_buf(),
                }),
            };
        }
    };

    let trimmed = content.trim();
    if !trimmed.contains(':') {
        return Err(CookieError::InvalidFormat {
            path: path.to_path_buf(),
        });
    }

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

/// Wait for the cookie file to become available.
///
/// Retries with exponential backoff (1s -> 30s, max 30 attempts ~ 5 min).
/// Only retries on `NotFound` (bitcoind may still be starting).
/// `PermissionDenied` and `InvalidFormat` fail immediately.
pub async fn wait_for_cookie(path: &Path) -> Result<(), CookieError> {
    let max_attempts = 30;
    let mut delay_secs = 1u64;
    let max_delay_secs = 30u64;

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
                    retry_in_secs = delay_secs,
                    "Cookie file not found, waiting for bitcoind to start"
                );
                tokio::time::sleep(std::time::Duration::from_secs(delay_secs)).await;
                delay_secs = (delay_secs * 2).min(max_delay_secs);
            }
            Err(e @ CookieError::PermissionDenied { .. }) => return Err(e),
            Err(e @ CookieError::InvalidFormat { .. }) => return Err(e),
        }
    }

    Err(CookieError::NotFound {
        path: path.to_path_buf(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;
    use std::os::unix::fs::PermissionsExt;

    #[test]
    fn resolve_cookie_path_cpunet() {
        let path = resolve_cookie_path(None, Network::CPUNet);
        let expected = PathBuf::from(shellexpand::tilde("~/.bitcoin/cpunet/.cookie").as_ref());
        assert_eq!(path, expected);
    }

    #[test]
    fn resolve_cookie_path_mainnet() {
        let path = resolve_cookie_path(None, Network::Bitcoin);
        let expected = PathBuf::from(shellexpand::tilde("~/.bitcoin/.cookie").as_ref());
        assert_eq!(path, expected);
    }

    #[test]
    fn resolve_cookie_path_testnet() {
        let path = resolve_cookie_path(None, Network::Testnet(bitcoin::TestnetVersion::V4));
        let expected = PathBuf::from(shellexpand::tilde("~/.bitcoin/testnet4/.cookie").as_ref());
        assert_eq!(path, expected);
    }

    #[test]
    fn resolve_cookie_path_signet() {
        let path = resolve_cookie_path(None, Network::Signet);
        let expected = PathBuf::from(shellexpand::tilde("~/.bitcoin/signet/.cookie").as_ref());
        assert_eq!(path, expected);
    }

    #[test]
    fn resolve_cookie_path_regtest() {
        let path = resolve_cookie_path(None, Network::Regtest);
        let expected = PathBuf::from(shellexpand::tilde("~/.bitcoin/regtest/.cookie").as_ref());
        assert_eq!(path, expected);
    }

    #[test]
    fn resolve_cookie_path_explicit_override() {
        let path = resolve_cookie_path(Some("/custom/path/.cookie"), Network::CPUNet);
        assert_eq!(path, PathBuf::from("/custom/path/.cookie"));
    }

    #[test]
    fn resolve_cookie_path_tilde_expansion() {
        let path = resolve_cookie_path(Some("~/my-bitcoin/.cookie"), Network::CPUNet);
        let expected = PathBuf::from(shellexpand::tilde("~/my-bitcoin/.cookie").as_ref());
        assert_eq!(path, expected);
    }

    #[test]
    fn resolve_ipc_socket_cpunet() {
        let socket = resolve_ipc_socket(None, Network::CPUNet);
        assert_eq!(socket, "/tmp/bitcoin-cpunet.sock");
    }

    #[test]
    fn resolve_ipc_socket_mainnet() {
        let socket = resolve_ipc_socket(None, Network::Bitcoin);
        assert_eq!(socket, "/tmp/bitcoin-main.sock");
    }

    #[test]
    fn resolve_ipc_socket_explicit_override() {
        let socket = resolve_ipc_socket(Some("/custom/socket.sock"), Network::CPUNet);
        assert_eq!(socket, "/custom/socket.sock");
    }

    #[test]
    fn validate_cookie_file_missing() {
        let result = validate_cookie_file(Path::new("/nonexistent/path/.cookie"));
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), CookieError::NotFound { .. }));
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
        // Should fail immediately, not retry
        assert!(elapsed.as_secs() < 2);
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
        assert!(elapsed.as_secs() < 2);
    }
}
