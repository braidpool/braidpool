use sqlx::{sqlite::SqliteConnectOptions, Executor, SqlitePool};
use std::{env, fs, path::Path, path::PathBuf, str::FromStr};

use crate::error::DBErrors;
#[allow(unused_imports)]
use tracing::{debug, error, info, trace, warn};
static SCHEMA_SQL: &str = include_str!("schema.sql");
static AUDIT_SCHEMA_SQL: &str = include_str!("audit_schema.sql");

/// Gets the braidpool data directory in a cross-platform manner.
fn get_data_dir() -> Result<PathBuf, DBErrors> {
    #[cfg(target_os = "linux")]
    {
        let home = env::var("HOME").map_err(|error| DBErrors::EnvVariableNotFetched {
            error: error.to_string(),
            var: "HOME".to_string(),
        })?;
        Ok(Path::new(&home).join(".braidpool"))
    }

    #[cfg(target_os = "macos")]
    {
        let home = env::var("HOME").map_err(|error| DBErrors::EnvVariableNotFetched {
            error: error.to_string(),
            var: "HOME".to_string(),
        })?;
        Ok(Path::new(&home)
            .join("Library")
            .join("Application Support")
            .join("braidpool"))
    }

    #[cfg(not(any(target_os = "linux", target_os = "macos")))]
    {
        Err(DBErrors::EnvVariableNotFetched {
            error: "this platform is not supported yet".to_string(),
            var: std::env::consts::OS.to_string(),
        })
    }
}

/// Initializes the bead database pool.
///
/// # Arguments
/// * `datadir` - Directory the database lives in, as resolved from `--datadir`.
///   When `None`, the platform default data directory is used.
///
/// # Returns
/// A connection pool to `<datadir>/braidpool.db`, creating the file and schema
/// if it does not exist yet.
///
/// # Errors
/// Returns a [`DBErrors`] when the data directory cannot be resolved or created,
/// or when the connection or schema initialization fails.
pub async fn init_db(datadir: Option<PathBuf>) -> Result<SqlitePool, DBErrors> {
    setup_sqlite_db(datadir, "braidpool.db", SCHEMA_SQL).await
}

/// Initializes the audit database pool.
///
/// # Arguments
/// * `datadir` - Directory the database lives in, as resolved from `--datadir`.
///   When `None`, the platform default data directory is used.
///
/// # Returns
/// A connection pool to `<datadir>/audit.db`, creating the file and schema if it
/// does not exist yet.
///
/// # Errors
/// Returns a [`DBErrors`] when the data directory cannot be resolved or created,
/// or when the connection or schema initialization fails.
pub async fn init_audit_db(datadir: Option<PathBuf>) -> Result<SqlitePool, DBErrors> {
    setup_sqlite_db(datadir, "audit.db", AUDIT_SCHEMA_SQL).await
}

async fn setup_sqlite_db(
    datadir: Option<PathBuf>,
    db_name: &str,
    schema_sql: &str,
) -> Result<SqlitePool, DBErrors> {
    // Honour `--datadir` when the caller resolved one, otherwise fall back to
    // the platform default data directory.
    let db_dir = match datadir {
        Some(dir) => dir,
        None => get_data_dir()?,
    };
    let db_path = db_dir.join(db_name);
    let dir_exists = db_dir.exists();

    // Create db directory if it doesn't exist
    if let Err(error) = fs::create_dir_all(&db_dir) {
        return Err(DBErrors::DBDirectoryNotCreated {
            error: error.to_string(),
            path: db_path,
        });
    } else if !dir_exists {
        info!(path = %db_dir.display(), "DB directory created successfully");
    }

    let db_exists = db_path.exists();
    let db_url = format!("sqlite://{}", db_path.to_string_lossy());
    // SQl connection configurations
    let db_config = match SqliteConnectOptions::from_str(&db_url) {
        Ok(config) => config,
        Err(error) => {
            return Err(DBErrors::ConnectionUrlNotParsed {
                error: error.to_string(),
                url: db_url.to_string(),
            });
        }
    };
    let sql_lite_connections = db_config
        .foreign_keys(true)
        .journal_mode(sqlx::sqlite::SqliteJournalMode::Wal);

    let pool = if db_exists {
        info!(db_path = %db_path.display(), "Using existing database");
        SqlitePool::connect_with(sql_lite_connections)
            .await
            .map_err(|error| DBErrors::ConnectionToSQlitePoolFailed {
                error: error.to_string(),
            })?
    } else {
        info!(db_path = %db_path.display(), "Creating new database");
        if let Err(e) = std::fs::File::create_new(&db_path) {
            error!(
                db_path = %db_path.display(),
                error = %e,
                "Failed to create database file"
            );
            return Err(DBErrors::DBDirectoryNotCreated {
                error: e.to_string(),
                path: db_path.clone(),
            });
        }

        let pool = SqlitePool::connect_with(sql_lite_connections)
            .await
            .map_err(|error| DBErrors::ConnectionToSQlitePoolFailed {
                error: error.to_string(),
            })?;

        pool.execute(schema_sql)
            .await
            .map_err(|error| DBErrors::SchemaNotInitialized {
                error: error.to_string(),
                db_path: db_path.clone(),
            })?;
        info!(db_path = %db_path.display(), "Database schema initialized");

        // Force WAL checkpoint to flush schema changes to disk
        match sqlx::query("PRAGMA wal_checkpoint(FULL)")
            .execute(&pool)
            .await
        {
            Ok(_) => {
                info!("WAL checkpoint completed successfully");
            }
            Err(error) => {
                warn!(error = ?error, "WAL checkpoint failed");
            }
        }
        pool
    };

    Ok(pool)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::{SystemTime, UNIX_EPOCH};

    /// Builds a unique, non-existent path under the system temp directory so
    /// concurrently running tests never share a database.
    fn unique_temp_dir(tag: &str) -> PathBuf {
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock before UNIX epoch")
            .as_nanos();
        env::temp_dir().join(format!(
            "braidpool-{}-{}-{}",
            tag,
            std::process::id(),
            nanos
        ))
    }

    #[tokio::test]
    async fn init_db_uses_supplied_datadir() {
        let datadir = unique_temp_dir("init-db");
        let pool = init_db(Some(datadir.clone()))
            .await
            .expect("database initialization failed");

        assert!(
            datadir.join("braidpool.db").exists(),
            "braidpool.db was not created inside the supplied datadir"
        );
        assert_ne!(
            datadir,
            get_data_dir().expect("default data dir not resolved"),
            "test datadir must not collide with the platform default"
        );

        pool.close().await;
        let _ = fs::remove_dir_all(&datadir);
    }

    #[tokio::test]
    async fn init_audit_db_uses_supplied_datadir() {
        let datadir = unique_temp_dir("init-audit-db");
        let pool = init_audit_db(Some(datadir.clone()))
            .await
            .expect("audit database initialization failed");

        assert!(
            datadir.join("audit.db").exists(),
            "audit.db was not created inside the supplied datadir"
        );

        pool.close().await;
        let _ = fs::remove_dir_all(&datadir);
    }

    #[tokio::test]
    async fn init_db_creates_missing_nested_datadir() {
        let root = unique_temp_dir("init-db-nested");
        let datadir = root.join("nested").join("state");
        let pool = init_db(Some(datadir.clone()))
            .await
            .expect("database initialization failed");

        assert!(
            datadir.join("braidpool.db").exists(),
            "nested datadir was not created"
        );

        pool.close().await;
        let _ = fs::remove_dir_all(&root);
    }

    /// With no datadir supplied the platform default (HOME-derived) is used.
    #[test]
    fn absent_datadir_falls_back_to_platform_default() {
        let home = env::var("HOME").expect("HOME must be set for this test");

        #[cfg(target_os = "linux")]
        let expected = Path::new(&home).join(".braidpool");

        #[cfg(target_os = "macos")]
        let expected = Path::new(&home)
            .join("Library")
            .join("Application Support")
            .join("braidpool");

        assert_eq!(
            get_data_dir().expect("default data dir not resolved"),
            expected
        );
    }
}
