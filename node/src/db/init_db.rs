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

pub async fn init_db() -> Result<SqlitePool, DBErrors> {
    setup_sqlite_db("braidpool.db", SCHEMA_SQL).await
}

pub async fn init_audit_db() -> Result<SqlitePool, DBErrors> {
    setup_sqlite_db("audit.db", AUDIT_SCHEMA_SQL).await
}

async fn setup_sqlite_db(db_name: &str, schema_sql: &str) -> Result<SqlitePool, DBErrors> {
    // Fetching the data directory
    let db_dir = get_data_dir()?;
    let db_path = db_dir.join(db_name);
    let dir_exists = db_dir.exists();

    // Create db directory if it doesn't exist
    if let Err(error) = fs::create_dir_all(&db_dir) {
        return Err(DBErrors::DBDirectoryNotCreated {
            error: error.to_string(),
            path: db_path,
        });
    } else if !dir_exists {
        info!("DB directory created successfully");
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
