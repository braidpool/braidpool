use sqlx::{sqlite::SqliteConnectOptions, Executor, SqlitePool};
use std::{env, fs, path::Path, str::FromStr};

use crate::error::DBErrors;
static SCHEMA_SQL: &str = include_str!("schema.sql");

pub async fn init_db() -> Result<SqlitePool, DBErrors> {
    //Fetching the home directory
    let home_dir = match env::var("HOME") {
        Ok(fetched_var) => fetched_var,
        Err(error) => {
            return Err(DBErrors::EnvVariableNotFetched {
                error: error.to_string(),
                var: "{HOME} Directory".to_string(),
            });
        }
    };
    let db_dir = Path::new(&home_dir).join(".braidpool");
    //Final db directory path
    let db_path = db_dir.join("braidpool.db");
    //Creating db directory
    match fs::create_dir_all(&db_dir) {
        Ok(_) => {
            log::info!("DB directory created successfully");
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
        log::info!("Database already exists at {:?}", db_path);
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
                log::info!("Schema initialized successfully at {:?}", db_path);
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
                log::info!("WAL checkpoint completed successfully");
            }
            Err(error) => {
                log::warn!("WAL checkpoint failed: {}", error);
            }
        }
        pool
    };

    Ok(conn)
}
