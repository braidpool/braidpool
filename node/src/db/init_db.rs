use sqlx::{sqlite::SqliteConnectOptions, Executor, SqlitePool};
use std::{fs, path::Path, str::FromStr};

use crate::error::DBErrors;
#[allow(unused_imports)]
use tracing::{debug, error, info, trace, warn};
static SCHEMA_SQL: &str = include_str!("schema.sql");
static AUDIT_SCHEMA_SQL: &str = include_str!("audit_schema.sql");

/// Initializes the braid database inside the node's data directory.
pub async fn init_db(datadir: &Path) -> Result<SqlitePool, DBErrors> {
    setup_sqlite_db(datadir, "braidpool.db", SCHEMA_SQL).await
}

/// Initializes the audit database inside the node's data directory.
pub async fn init_audit_db(datadir: &Path) -> Result<SqlitePool, DBErrors> {
    setup_sqlite_db(datadir, "audit.db", AUDIT_SCHEMA_SQL).await
}

async fn setup_sqlite_db(
    db_dir: &Path,
    db_name: &str,
    schema_sql: &str,
) -> Result<SqlitePool, DBErrors> {
    let db_path = db_dir.join(db_name);
    let dir_exists = db_dir.exists();

    // Create db directory if it doesn't exist
    if let Err(error) = fs::create_dir_all(db_dir) {
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
    use std::path::PathBuf;
    use std::sync::atomic::{AtomicU64, Ordering};

    fn unique_dir() -> PathBuf {
        static COUNTER: AtomicU64 = AtomicU64::new(0);
        let dir = std::env::temp_dir().join(format!(
            "braidpool-initdb-{}-{}",
            std::process::id(),
            COUNTER.fetch_add(1, Ordering::Relaxed)
        ));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).unwrap();
        dir
    }

    /// SQL inserting one `Bead` row whose key and signature have the given byte lengths.
    fn bead_row_sql(key_len: usize, signature_len: usize) -> String {
        format!(
            "INSERT INTO Bead (hash, hashPrevBlock, hashMerkleRoot, payout_address, \
             start_timestamp, comm_pub_key, miner_ip, extranonce1, extranonce2, \
             broadcast_timestamp, signature) \
             VALUES (x'01', x'02', x'03', x'04', 1, zeroblob({key_len}), 'ip', 'a', 'b', 2, \
             zeroblob({signature_len}))"
        )
    }

    /// SQL inserting one `AuditBead` row whose key and signature have the given byte lengths.
    fn audit_bead_row_sql(key_len: usize, signature_len: usize) -> String {
        format!(
            "INSERT INTO AuditBead (composite_hash, block_hash, version, prev_block_hash, \
             merkle_root, timestamp, bits, nonce, payout_address, start_timestamp, \
             comm_pub_key, min_target, weak_target, miner_ip, extranonce1, extranonce2, \
             broadcast_timestamp, signature, created_at) \
             VALUES (x'01', x'02', 1, x'03', x'04', 1, 1, 1, 'a', 1, zeroblob({key_len}), 1, 1, \
             'ip', 'a', 'b', 2, zeroblob({signature_len}), 1)"
        )
    }

    #[tokio::test]
    async fn bead_table_accepts_exactly_32_byte_keys_and_64_byte_signatures() {
        let dir = unique_dir();
        let pool = init_db(&dir).await.unwrap();
        pool.execute(&*bead_row_sql(32, 64)).await.unwrap();
        let _ = fs::remove_dir_all(&dir);
    }

    #[tokio::test]
    async fn bead_table_refuses_a_key_or_signature_of_the_old_size() {
        let dir = unique_dir();
        let pool = init_db(&dir).await.unwrap();
        // 33-byte compressed key, 65-byte uncompressed key, and one byte short or long
        for key_len in [0, 31, 33, 65] {
            assert!(
                pool.execute(&*bead_row_sql(key_len, 64)).await.is_err(),
                "a {key_len}-byte key must be refused"
            );
        }
        // DER signatures are 70 to 72 bytes; also one byte short or long
        for signature_len in [0, 63, 65, 70, 71, 72] {
            assert!(
                pool.execute(&*bead_row_sql(32, signature_len))
                    .await
                    .is_err(),
                "a {signature_len}-byte signature must be refused"
            );
        }
        let _ = fs::remove_dir_all(&dir);
    }

    #[tokio::test]
    async fn audit_bead_table_has_the_same_length_checks() {
        let dir = unique_dir();
        let pool = init_audit_db(&dir).await.unwrap();
        pool.execute(&*audit_bead_row_sql(32, 64)).await.unwrap();
        // a second row needs different unique values, so rebuild the table state per case
        for (key_len, signature_len) in [(33, 64), (32, 70)] {
            let sql =
                audit_bead_row_sql(key_len, signature_len).replace("x'01', x'02'", "x'05', x'06'");
            assert!(
                pool.execute(&*sql).await.is_err(),
                "key {key_len} / signature {signature_len} must be refused"
            );
        }
        let _ = fs::remove_dir_all(&dir);
    }
}
