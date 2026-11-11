//! Creating and loading node secret files such as the miner secp256k1 key.
//!
//! * A new file is created owner-read-only (`0o400`): it is written to a temporary sibling
//!   with that mode, then published with `hard_link`, which fails if the destination exists.
//!   The secret never exists with wider permissions, never appears half-written, and two
//!   processes starting at once cannot overwrite each other's key.
//! * Only a missing file (`NotFound`) causes a new secret to be generated. Any other read
//!   error aborts, so an identity is never silently replaced.
//! * An existing file must be a regular file; a mode other than `0o400` is tightened with a
//!   warning.

use std::fs::{self, File, OpenOptions};
use std::io::{self, ErrorKind, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};
use tracing::warn;

/// Unix mode of every secret file: owner read-only.
pub const SECRET_FILE_MODE: u32 = 0o400;

/// Read the secret at `path`, or create it with `generate` if the file does not exist.
///
/// Returns the secret bytes and `true` if this call created the file. If another process
/// creates the file concurrently, its secret is returned instead of ours.
///
/// # Errors
/// Any read error other than `NotFound`, a path that is not a regular file, or a failure to
/// generate or write the new secret.
pub fn read_or_create_secret(
    path: &Path,
    generate: impl FnOnce() -> io::Result<Vec<u8>>,
) -> io::Result<(Vec<u8>, bool)> {
    if let Some(bytes) = read_existing(path)? {
        return Ok((bytes, false));
    }
    let secret = generate()?;
    match write_new_secret(path, &secret) {
        Ok(()) => Ok((secret, true)),
        Err(e) if e.kind() == ErrorKind::AlreadyExists => match read_existing(path)? {
            Some(bytes) => Ok((bytes, false)),
            None => Err(io::Error::new(
                ErrorKind::NotFound,
                format!("{} disappeared while being created", path.display()),
            )),
        },
        Err(e) => Err(e),
    }
}

fn read_existing(path: &Path) -> io::Result<Option<Vec<u8>>> {
    let meta = match fs::metadata(path) {
        Ok(meta) => meta,
        Err(e) if e.kind() == ErrorKind::NotFound => return Ok(None),
        Err(e) => return Err(e),
    };
    if !meta.is_file() {
        return Err(io::Error::new(
            ErrorKind::InvalidData,
            format!("{} exists but is not a regular file", path.display()),
        ));
    }
    restrict_permissions(path, &meta)?;
    match fs::read(path) {
        Ok(bytes) => Ok(Some(bytes)),
        Err(e) if e.kind() == ErrorKind::NotFound => Ok(None),
        Err(e) => Err(e),
    }
}

#[cfg(unix)]
fn restrict_permissions(path: &Path, meta: &fs::Metadata) -> io::Result<()> {
    use std::os::unix::fs::PermissionsExt;
    let mode = meta.permissions().mode() & 0o777;
    if mode != SECRET_FILE_MODE {
        warn!(
            path = %path.display(),
            mode = format!("{mode:o}"),
            "Secret file permissions are not 0o400; tightening them"
        );
        let mut perms = meta.permissions();
        perms.set_mode(SECRET_FILE_MODE);
        fs::set_permissions(path, perms)?;
    }
    Ok(())
}

#[cfg(not(unix))]
fn restrict_permissions(_path: &Path, _meta: &fs::Metadata) -> io::Result<()> {
    Ok(())
}

fn open_new(path: &Path) -> io::Result<File> {
    let mut opts = OpenOptions::new();
    opts.write(true).create_new(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::OpenOptionsExt;
        opts.mode(SECRET_FILE_MODE);
    }
    opts.open(path)
}

/// Process-wide counter so concurrent callers never pick the same temporary name, even when
/// the clock resolution is too coarse to tell their timestamps apart.
static TEMP_COUNTER: AtomicU64 = AtomicU64::new(0);

/// Sibling path used while the secret is being written. Unique per call.
fn temp_sibling(path: &Path) -> PathBuf {
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or_default();
    let n = TEMP_COUNTER.fetch_add(1, Ordering::Relaxed);
    let mut name = path
        .file_name()
        .map(|n| n.to_os_string())
        .unwrap_or_default();
    name.push(format!(".tmp-{}-{nanos}-{n}", std::process::id()));
    path.with_file_name(name)
}

fn write_all_synced(path: &Path, bytes: &[u8]) -> io::Result<()> {
    let mut file = open_new(path)?;
    file.write_all(bytes)?;
    file.sync_all()
}

fn write_temp(path: &Path, bytes: &[u8]) -> io::Result<PathBuf> {
    let mut last = None;
    for _ in 0..8 {
        let tmp = temp_sibling(path);
        match write_all_synced(&tmp, bytes) {
            Ok(()) => return Ok(tmp),
            Err(e) if e.kind() == ErrorKind::AlreadyExists => last = Some(e),
            Err(e) => {
                let _ = fs::remove_file(&tmp);
                return Err(e);
            }
        }
    }
    Err(last.unwrap_or_else(|| io::Error::other("could not create a temporary file")))
}

fn write_new_secret(path: &Path, bytes: &[u8]) -> io::Result<()> {
    let tmp = write_temp(path, bytes)?;
    let published = fs::hard_link(&tmp, path);
    let _ = fs::remove_file(&tmp);
    match published {
        Ok(()) => {
            sync_parent(path);
            Ok(())
        }
        Err(e) if e.kind() == ErrorKind::AlreadyExists => Err(e),
        Err(_) => {
            write_all_synced(path, bytes)?;
            sync_parent(path);
            Ok(())
        }
    }
}

/// Best-effort durability of the directory entry.
fn sync_parent(path: &Path) {
    if let Some(parent) = path.parent() {
        if let Ok(dir) = File::open(parent) {
            let _ = dir.sync_all();
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::{Arc, Barrier};
    use std::thread;

    fn unique_dir(tag: &str) -> PathBuf {
        // The counter keeps parallel tests apart even where the clock resolution is coarse.
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let n = COUNTER.fetch_add(1, Ordering::Relaxed);
        let dir = std::env::temp_dir().join(format!(
            "braidpool-secret-file-{tag}-{}-{nanos}-{n}",
            std::process::id()
        ));
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    fn entries(dir: &Path) -> Vec<String> {
        let mut names: Vec<String> = fs::read_dir(dir)
            .unwrap()
            .map(|e| e.unwrap().file_name().to_string_lossy().into_owned())
            .collect();
        names.sort();
        names
    }

    #[test]
    fn creates_file_and_returns_secret() {
        let dir = unique_dir("create");
        let path = dir.join("secret");
        let (bytes, created) = read_or_create_secret(&path, || Ok(vec![7u8; 32])).unwrap();
        assert!(created);
        assert_eq!(bytes, vec![7u8; 32]);
        assert_eq!(fs::read(&path).unwrap(), vec![7u8; 32]);
        let _ = fs::remove_dir_all(&dir);
    }

    #[cfg(unix)]
    #[test]
    fn new_file_is_owner_read_only() {
        use std::os::unix::fs::PermissionsExt;
        let dir = unique_dir("mode");
        let path = dir.join("secret");
        read_or_create_secret(&path, || Ok(vec![1u8; 32])).unwrap();
        let mode = fs::metadata(&path).unwrap().permissions().mode() & 0o777;
        assert_eq!(mode, 0o400);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn second_call_reuses_existing_secret_and_does_not_generate() {
        let dir = unique_dir("reuse");
        let path = dir.join("secret");
        read_or_create_secret(&path, || Ok(vec![1u8; 32])).unwrap();
        let (bytes, created) = read_or_create_secret(&path, || {
            panic!("generate must not run when the file exists")
        })
        .unwrap();
        assert!(!created);
        assert_eq!(bytes, vec![1u8; 32]);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn leaves_no_temporary_files_behind() {
        let dir = unique_dir("tmp");
        let path = dir.join("secret");
        read_or_create_secret(&path, || Ok(vec![1u8; 32])).unwrap();
        assert_eq!(entries(&dir), vec!["secret".to_string()]);
        let _ = fs::remove_dir_all(&dir);
    }

    #[cfg(unix)]
    #[test]
    fn permissive_existing_file_is_tightened() {
        use std::os::unix::fs::PermissionsExt;
        let dir = unique_dir("tighten");
        let path = dir.join("secret");
        fs::write(&path, [9u8; 32]).unwrap();
        fs::set_permissions(&path, fs::Permissions::from_mode(0o644)).unwrap();
        let (bytes, created) =
            read_or_create_secret(&path, || panic!("must not generate")).unwrap();
        assert!(!created);
        assert_eq!(bytes, vec![9u8; 32]);
        let mode = fs::metadata(&path).unwrap().permissions().mode() & 0o777;
        assert_eq!(mode, 0o400);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn directory_in_place_of_file_is_an_error_not_a_new_secret() {
        let dir = unique_dir("isdir");
        let path = dir.join("secret");
        fs::create_dir(&path).unwrap();
        let result = read_or_create_secret(&path, || panic!("must not generate"));
        assert_eq!(result.unwrap_err().kind(), ErrorKind::InvalidData);
        assert!(path.is_dir());
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn generate_failure_creates_nothing() {
        let dir = unique_dir("genfail");
        let path = dir.join("secret");
        let result = read_or_create_secret(&path, || Err(io::Error::other("no entropy")));
        assert!(result.is_err());
        assert!(entries(&dir).is_empty());
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn missing_parent_directory_is_an_error() {
        let dir = unique_dir("noparent");
        let path = dir.join("missing").join("secret");
        let result = read_or_create_secret(&path, || Ok(vec![1u8; 32]));
        assert_eq!(result.unwrap_err().kind(), ErrorKind::NotFound);
        let _ = fs::remove_dir_all(&dir);
    }

    #[test]
    fn concurrent_first_run_produces_one_secret() {
        let dir = unique_dir("race");
        let path = Arc::new(dir.join("secret"));
        let threads = 8;
        let barrier = Arc::new(Barrier::new(threads));
        let handles: Vec<_> = (0..threads)
            .map(|i| {
                let path = Arc::clone(&path);
                let barrier = Arc::clone(&barrier);
                thread::spawn(move || {
                    barrier.wait();
                    // each thread would generate a different secret
                    read_or_create_secret(&path, || Ok(vec![i as u8; 32])).unwrap()
                })
            })
            .collect();
        let results: Vec<(Vec<u8>, bool)> =
            handles.into_iter().map(|h| h.join().unwrap()).collect();
        let on_disk = fs::read(&*path).unwrap();
        assert!(results.iter().all(|(bytes, _)| *bytes == on_disk));
        assert_eq!(results.iter().filter(|(_, created)| *created).count(), 1);
        assert_eq!(entries(&dir), vec!["secret".to_string()]);
        let _ = fs::remove_dir_all(&dir);
    }
}
