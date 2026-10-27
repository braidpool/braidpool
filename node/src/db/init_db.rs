use sqlx::{sqlite::SqliteConnectOptions, Executor, SqlitePool};
use std::{fs, path::Path, str::FromStr};

use crate::error::DBErrors;
#[allow(unused_imports)]
use tracing::{debug, error, info, trace, warn};
static SCHEMA_SQL: &str = include_str!("schema.sql");
static AUDIT_SCHEMA_SQL: &str = include_str!("audit_schema.sql");

/// On-disk format version, stored in SQLite's `PRAGMA user_version`.
///
/// Version 2 is the protocol 2.0.0 bead format: 32-byte BIP340 x-only keys and 64-byte Schnorr
/// signatures. Databases created before versioning report 0 and hold 33-byte ECDSA-era keys
/// and DER signatures, which this node cannot decode.
pub const DB_FORMAT_VERSION: i64 = 2;

/// Initializes the braid database inside the node's data directory.
pub async fn init_db(datadir: &Path) -> Result<SqlitePool, DBErrors> {
    setup_sqlite_db(datadir, "braidpool.db", SCHEMA_SQL, "Bead").await
}

/// Initializes the audit database inside the node's data directory.
pub async fn init_audit_db(datadir: &Path) -> Result<SqlitePool, DBErrors> {
    setup_sqlite_db(datadir, "audit.db", AUDIT_SCHEMA_SQL, "AuditBead").await
}

async fn setup_sqlite_db(
    db_dir: &Path,
    db_name: &str,
    schema_sql: &str,
    bead_table: &str,
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
        let pool = SqlitePool::connect_with(sql_lite_connections)
            .await
            .map_err(|error| DBErrors::ConnectionToSQlitePoolFailed {
                error: error.to_string(),
            })?;
        check_db_format(&pool, &db_path, schema_sql, bead_table).await?;
        pool
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
        set_db_format_version(&pool, &db_path).await?;
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

async fn set_db_format_version(pool: &SqlitePool, db_path: &Path) -> Result<(), DBErrors> {
    // PRAGMA does not accept bound parameters; the value is a constant.
    pool.execute(format!("PRAGMA user_version = {DB_FORMAT_VERSION}").as_str())
        .await
        .map(|_| ())
        .map_err(|error| DBErrors::SchemaNotInitialized {
            error: error.to_string(),
            db_path: db_path.to_path_buf(),
        })
}

/// Refuse to open a database written by another format version.
///
/// A database from before versioning (`user_version` 0) that holds no beads is rebuilt with the
/// current schema (see [`rebuild_schema`]) and stamped with the current version. One that holds
/// beads cannot be read, and the operator is told what to do instead of the node failing later
/// with a decode error on the first row.
///
/// # Errors
/// [`DBErrors::IncompatibleDatabase`] for a newer database or an older one that holds beads,
/// [`DBErrors::TupleNotFetched`] if the version or bead count cannot be read, or
/// [`DBErrors::SchemaNotInitialized`] if the rebuild or the version stamp fails.
async fn check_db_format(
    pool: &SqlitePool,
    db_path: &Path,
    schema_sql: &str,
    bead_table: &str,
) -> Result<(), DBErrors> {
    let incompatible = |found_version: i64, detail: &str| DBErrors::IncompatibleDatabase {
        db_path: db_path.to_path_buf(),
        found_version,
        expected_version: DB_FORMAT_VERSION,
        detail: detail.to_string(),
    };
    let found_version: i64 = sqlx::query_scalar("PRAGMA user_version")
        .fetch_one(pool)
        .await
        .map_err(|error| DBErrors::TupleNotFetched {
            error: error.to_string(),
        })?;
    if found_version == DB_FORMAT_VERSION {
        return Ok(());
    }
    if found_version > DB_FORMAT_VERSION {
        return Err(incompatible(
            found_version,
            "it was written by a newer version of the node; upgrade the node",
        ));
    }
    let table_exists: i64 =
        sqlx::query_scalar("SELECT COUNT(*) FROM sqlite_master WHERE type = 'table' AND name = ?")
            .bind(bead_table)
            .fetch_one(pool)
            .await
            .map_err(|error| DBErrors::TupleNotFetched {
                error: error.to_string(),
            })?;
    if table_exists > 0 {
        // The table name is one of two internal constants, never user input.
        let has_beads: i64 = sqlx::query_scalar(&format!(
            "SELECT EXISTS(SELECT 1 FROM {bead_table} LIMIT 1)"
        ))
        .fetch_one(pool)
        .await
        .map_err(|error| DBErrors::TupleNotFetched {
            error: error.to_string(),
        })?;
        if has_beads != 0 {
            return Err(incompatible(
                found_version,
                "it holds beads from before protocol 2.0.0 (33-byte ECDSA keys and DER \
                 signatures), which cannot be read. Stop the node and delete this file (and its \
                 -wal and -shm files) to start from an empty braid",
            ));
        }
    }
    rebuild_schema(pool, db_path, schema_sql).await?;
    set_db_format_version(pool, db_path).await
}

/// Replace every table and view of an empty pre-versioning database with the current schema.
///
/// `CREATE TABLE IF NOT EXISTS` leaves an existing table as it is, so re-running the schema
/// would keep the old tables without the version-2 length checks, and two databases stamped
/// version 2 would enforce different rules. The caller has checked that no beads are stored,
/// so nothing of value is dropped: every other table either references beads or is derived
/// from them. Indexes go with their tables.
///
/// The drops run in one transaction. The schema itself runs afterwards, because it sets
/// `journal_mode`, which SQLite refuses inside a transaction. If the node stops in between,
/// the database is still unversioned and empty, so the next start rebuilds it again.
///
/// # Errors
/// [`DBErrors::TupleNotFetched`] if the existing objects cannot be listed, or
/// [`DBErrors::SchemaNotInitialized`] if a drop or the new schema fails.
async fn rebuild_schema(
    pool: &SqlitePool,
    db_path: &Path,
    schema_sql: &str,
) -> Result<(), DBErrors> {
    let schema_error = |error: sqlx::Error| DBErrors::SchemaNotInitialized {
        error: error.to_string(),
        db_path: db_path.to_path_buf(),
    };
    // Views first: a view may select from a table that is about to be dropped.
    let objects: Vec<(String, String)> = sqlx::query_as(
        "SELECT type, name FROM sqlite_master \
         WHERE type IN ('view', 'table') AND name NOT LIKE 'sqlite_%' \
         ORDER BY type = 'table', name",
    )
    .fetch_all(pool)
    .await
    .map_err(|error| DBErrors::TupleNotFetched {
        error: error.to_string(),
    })?;
    info!(
        db_path = %db_path.display(),
        objects = objects.len(),
        "Rebuilding empty pre-versioning database with the current schema"
    );
    let mut tx = pool.begin().await.map_err(schema_error)?;
    for (kind, name) in &objects {
        // The names come from the database file, so quote them as SQL identifiers.
        let statement = format!(
            "DROP {} IF EXISTS \"{}\"",
            if kind == "view" { "VIEW" } else { "TABLE" },
            name.replace('"', "\"\"")
        );
        (&mut *tx)
            .execute(statement.as_str())
            .await
            .map_err(schema_error)?;
    }
    tx.commit().await.map_err(schema_error)?;
    pool.execute(schema_sql).await.map_err(schema_error)?;
    Ok(())
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

    async fn user_version(pool: &SqlitePool) -> i64 {
        sqlx::query_scalar("PRAGMA user_version")
            .fetch_one(pool)
            .await
            .unwrap()
    }

    /// Insert one bead row with a 33-byte key and a DER-length signature, as old nodes wrote.
    /// New databases refuse such a row (see the length checks), so the checks are switched off
    /// for this insert, the way a database created before they existed would hold it.
    async fn insert_legacy_bead(pool: &SqlitePool, table: &str) {
        if table != "Bead" {
            return;
        }
        // The pragma is per connection, so use one connection for both statements.
        let mut connection = pool.acquire().await.unwrap();
        connection
            .execute("PRAGMA ignore_check_constraints = ON")
            .await
            .unwrap();
        connection.execute(&*bead_row_sql(33, 70)).await.unwrap();
        connection
            .execute("PRAGMA ignore_check_constraints = OFF")
            .await
            .unwrap();
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
    async fn new_database_is_stamped_with_the_current_version() {
        let dir = unique_dir();
        let pool = init_db(&dir).await.unwrap();
        assert_eq!(user_version(&pool).await, DB_FORMAT_VERSION);
        let _ = fs::remove_dir_all(&dir);
    }

    #[tokio::test]
    async fn current_version_database_reopens() {
        let dir = unique_dir();
        init_db(&dir).await.unwrap().close().await;
        let pool = init_db(&dir).await.unwrap();
        assert_eq!(user_version(&pool).await, DB_FORMAT_VERSION);
        let _ = fs::remove_dir_all(&dir);
    }

    #[tokio::test]
    async fn legacy_database_with_beads_is_refused_with_instructions() {
        let dir = unique_dir();
        let pool = init_db(&dir).await.unwrap();
        insert_legacy_bead(&pool, "Bead").await;
        pool.execute("PRAGMA user_version = 0").await.unwrap(); // as an unversioned database
        pool.close().await;
        let err = init_db(&dir).await.unwrap_err();
        match &err {
            DBErrors::IncompatibleDatabase {
                found_version,
                expected_version,
                detail,
                ..
            } => {
                assert_eq!(*found_version, 0);
                assert_eq!(*expected_version, DB_FORMAT_VERSION);
                assert!(detail.contains("delete"), "{detail}");
            }
            other => panic!("expected IncompatibleDatabase, got {other:?}"),
        }
        assert!(err.to_string().contains("version 0"));
        let _ = fs::remove_dir_all(&dir);
    }

    #[tokio::test]
    async fn legacy_database_without_beads_is_upgraded_in_place() {
        let dir = unique_dir();
        let pool = init_db(&dir).await.unwrap();
        pool.execute("PRAGMA user_version = 0").await.unwrap();
        pool.close().await;
        let pool = init_db(&dir).await.unwrap();
        assert_eq!(user_version(&pool).await, DB_FORMAT_VERSION);
        let _ = fs::remove_dir_all(&dir);
    }

    /// Create `db_name` in `dir` the way a node before versioning did: the schema without the
    /// version-2 length checks, and `user_version` 0.
    async fn create_unversioned_db(dir: &Path, db_name: &str, schema_sql: &str) -> SqlitePool {
        let legacy_schema = schema_sql
            .replace(" CHECK (length(comm_pub_key) = 32)", "")
            .replace(" CHECK (length(signature) = 64)", "");
        assert!(
            !legacy_schema.contains("CHECK (length("),
            "the length checks in the schema changed; update this helper"
        );
        let url = format!("sqlite://{}", dir.join(db_name).to_string_lossy());
        let options = SqliteConnectOptions::from_str(&url)
            .unwrap()
            .create_if_missing(true);
        let pool = SqlitePool::connect_with(options).await.unwrap();
        pool.execute(legacy_schema.as_str()).await.unwrap();
        pool
    }

    async fn object_exists(pool: &SqlitePool, kind: &str, name: &str) -> bool {
        let count: i64 =
            sqlx::query_scalar("SELECT COUNT(*) FROM sqlite_master WHERE type = ? AND name = ?")
                .bind(kind)
                .bind(name)
                .fetch_one(pool)
                .await
                .unwrap();
        count == 1
    }

    #[tokio::test]
    async fn unversioned_empty_database_is_rebuilt_with_the_length_checks() {
        let dir = unique_dir();
        let legacy = create_unversioned_db(&dir, "braidpool.db", SCHEMA_SQL).await;
        // The old schema accepts a 33-byte key, so the rebuild below is what adds the check.
        legacy.execute(&*bead_row_sql(33, 64)).await.unwrap();
        legacy.execute("DELETE FROM Bead").await.unwrap();
        legacy.close().await;

        let pool = init_db(&dir).await.unwrap();
        assert_eq!(user_version(&pool).await, DB_FORMAT_VERSION);
        assert!(pool.execute(&*bead_row_sql(33, 64)).await.is_err());
        assert!(pool.execute(&*bead_row_sql(32, 70)).await.is_err());
        pool.execute(&*bead_row_sql(32, 64)).await.unwrap();
        // Views and indexes are recreated with the tables.
        assert!(object_exists(&pool, "view", "Orphans").await);
        assert!(object_exists(&pool, "index", "bead_hash").await);
        let _ = fs::remove_dir_all(&dir);
    }

    #[tokio::test]
    async fn unversioned_empty_audit_database_is_rebuilt_with_the_length_checks() {
        let dir = unique_dir();
        create_unversioned_db(&dir, "audit.db", AUDIT_SCHEMA_SQL)
            .await
            .close()
            .await;

        let pool = init_audit_db(&dir).await.unwrap();
        assert_eq!(user_version(&pool).await, DB_FORMAT_VERSION);
        assert!(pool.execute(&*audit_bead_row_sql(33, 64)).await.is_err());
        pool.execute(&*audit_bead_row_sql(32, 64)).await.unwrap();
        assert!(object_exists(&pool, "view", "AuditTips").await);
        let _ = fs::remove_dir_all(&dir);
    }

    #[tokio::test]
    async fn newer_database_is_refused() {
        let dir = unique_dir();
        let pool = init_db(&dir).await.unwrap();
        pool.execute("PRAGMA user_version = 99").await.unwrap();
        pool.close().await;
        let err = init_db(&dir).await.unwrap_err();
        assert!(matches!(
            err,
            DBErrors::IncompatibleDatabase {
                found_version: 99,
                ..
            }
        ));
        let _ = fs::remove_dir_all(&dir);
    }

    #[tokio::test]
    async fn audit_database_is_versioned_too() {
        let dir = unique_dir();
        let pool = init_audit_db(&dir).await.unwrap();
        assert_eq!(user_version(&pool).await, DB_FORMAT_VERSION);
        let _ = fs::remove_dir_all(&dir);
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
