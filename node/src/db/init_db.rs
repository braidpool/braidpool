use sqlx::{sqlite::SqliteConnectOptions, Executor, SqlitePool};
use std::{env, fs, path::Path, path::PathBuf, str::FromStr};

use crate::error::DBErrors;
#[allow(unused_imports)]
use tracing::{debug, error, info, trace, warn};
static SCHEMA_SQL: &str = include_str!("schema.sql");

/// Initialize the sqlite pool for a given network-scoped data directory.
///
/// The DB lives at `<network_datadir>/braidpool.db`. The caller is expected to
/// pass the per-network subdirectory (e.g. `~/.braidpool/cpunet`) so that the
/// same binary running against different networks never shares state.
pub async fn init_db(network_datadir: PathBuf, network: &str) -> Result<SqlitePool, DBErrors> {
    // One-time courtesy warning for the pre-network layout. If an operator
    // upgrades from the old hardcoded layout, point them at the new location
    // and leave the old file alone (clean-break, no auto-migration).
    if let Ok(home_dir) = env::var("HOME") {
        let legacy_path = Path::new(&home_dir).join(".braidpool").join("braidpool.db");
        let new_path = network_datadir.join("braidpool.db");
        if legacy_path.exists() && legacy_path != new_path && !new_path.exists() {
            warn!(
                legacy = %legacy_path.display(),
                new = %new_path.display(),
                network = %network,
                "Legacy braidpool DB found outside the network-scoped data directory. \
                 It is no longer used; move or delete it to silence this warning."
            );
        }
    }

    //Final db directory path
    let db_path = network_datadir.join("braidpool.db");
    //Creating db directory if it doesn't exist
    let dir_exists = network_datadir.exists();
    match fs::create_dir_all(&network_datadir) {
        Ok(_) => {
            if !dir_exists {
                info!(path = %network_datadir.display(), "DB directory created successfully");
            }
        }
        Err(error) => {
            return Err(DBErrors::DBDirectoryNotCreated {
                error: error.to_string(),
                path: db_path,
            });
        }
    };
    //sqlite db url
    let db_url = format!("sqlite://{}", db_path.to_string_lossy());
    let db_exists = db_path.exists();
    //SQl connection configurations
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
    //Initializing connection to existing DB
    let conn = if db_exists {
        info!(
            db_path = %db_path.display(),
            "Using existing database"
        );
        let pool = match SqlitePool::connect_with(sql_lite_connections).await {
            Ok(initialized_pool) => initialized_pool,
            Err(error) => {
                return Err(DBErrors::ConnectionToSQlitePoolFailed {
                    error: error.to_string(),
                });
            }
        };
        pool
    } else {
        let _file = std::fs::File::create_new(db_path.clone());
        let pool = match SqlitePool::connect_with(sql_lite_connections).await {
            Ok(initialized_pool) => initialized_pool,
            Err(error) => {
                return Err(DBErrors::ConnectionToSQlitePoolFailed {
                    error: error.to_string(),
                });
            }
        };
        let _query_result = match pool.execute(SCHEMA_SQL).await {
            Ok(_res) => {
                info!(
                    db_path = %db_path.display(),
                    "Database schema initialized"
                );
            }
            Err(error) => {
                return Err(DBErrors::SchemaNotInitialized {
                    error: error.to_string(),
                    db_path: db_path,
                })
            }
        };

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

    Ok(conn)
}
