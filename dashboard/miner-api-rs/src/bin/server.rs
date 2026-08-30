use std::net::SocketAddr;
use std::sync::Arc;

use miner_api_rs::{api, config::Config, db};
use tokio::signal;
use tokio::sync::broadcast;
use tracing::info;

#[tokio::main]
async fn main() -> anyhow::Result<()> {
    tracing_subscriber::fmt()
        .with_env_filter(
            tracing_subscriber::EnvFilter::from_default_env()
                .add_directive("miner_api_rs=info".parse()?)
                .add_directive("tower_http=info".parse()?),
        )
        .init();

    let config = Config::from_env();
    info!(port = config.port, db = %config.db_path, "starting miner-api-rs");

    let pool = db::init_db(&config.db_path).await?;
    let port = config.port;
    let refresh_secs = config.refresh_interval_secs;
    let scan_secs = config.scan_interval_secs;
    let timeout_secs = config.miner_timeout_secs;
    let config_max_concurrent = config.max_concurrent_probes;

    // Broadcast channel: background tasks push JSON to all connected WS clients.
    let (broadcast_tx, _) = broadcast::channel::<String>(64);

    let state = Arc::new(api::AppState {
        pool: pool.clone(),
        config,
        broadcast_tx: broadcast_tx.clone(),
    });

    let router = api::build_router(Arc::clone(&state));

    //  background periodic refresh
    {
        let pool = pool.clone();
        let tx = broadcast_tx.clone();
        tokio::spawn(async move {
            let mut interval = tokio::time::interval(std::time::Duration::from_secs(refresh_secs));
            interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
            interval.tick().await; // skip first immediate tick

            loop {
                interval.tick().await;
                info!("periodic refresh starting");
                match miner_api_rs::db::service::refresh_all(
                    &pool,
                    timeout_secs,
                    config_max_concurrent,
                )
                .await
                {
                    Ok(s) => {
                        info!(
                            success = s.success,
                            failed = s.failed,
                            "periodic refresh done"
                        );
                        broadcast_miners(&pool, &tx).await;
                    }
                    Err(e) => tracing::error!(error = %e, "periodic refresh error"),
                }
            }
        });
    }

    // background periodic LAN scan
    {
        let pool = pool.clone();
        let tx = broadcast_tx.clone();
        tokio::spawn(async move {
            // Delay first scan so the server is fully up before probing.
            tokio::time::sleep(std::time::Duration::from_secs(10)).await;

            let mut interval = tokio::time::interval(std::time::Duration::from_secs(scan_secs));
            interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);

            loop {
                interval.tick().await;
                info!("periodic LAN scan starting");
                let miners = miner_api_rs::scanner::scan_lan().await;
                let found = miners.len();
                let mut added = 0usize;

                for miner in &miners {
                    let ip = miner.get_ip();
                    // Use the already-identified handle — no second probe needed.
                    let data =
                        miner_api_rs::miner_service::normalize_handle(miner.as_ref(), timeout_secs)
                            .await;
                    match miner_api_rs::db::service::upsert_discovered(&pool, ip, &data).await {
                        Ok(true) => added += 1,
                        Ok(false) => {}
                        Err(e) => {
                            tracing::warn!(ip = %ip, error = %e, "upsert failed")
                        }
                    }
                }

                info!(found, added, "periodic LAN scan done");
                if added > 0 {
                    broadcast_miners(&pool, &tx).await;
                }
            }
        });
    }

    //  bind and serve
    let addr = SocketAddr::from(([0, 0, 0, 0], port));
    info!(addr = %addr, "listening");

    let listener = tokio::net::TcpListener::bind(addr).await?;
    axum::serve(listener, router)
        .with_graceful_shutdown(shutdown_signal())
        .await?;

    Ok(())
}

/// Fetch all miners from the DB and broadcast the list to connected WebSocket clients.
async fn broadcast_miners(pool: &sqlx::SqlitePool, tx: &tokio::sync::broadcast::Sender<String>) {
    match miner_api_rs::db::service::get_all(pool).await {
        Ok(miners) => {
            let list: Vec<serde_json::Value> = miners.iter().map(|m| m.to_json()).collect();
            let msg = serde_json::to_string(&serde_json::json!({
                "success": true,
                "miners":  list,
            }))
            .unwrap_or_default();
            let _ = tx.send(msg);
        }
        Err(e) => tracing::warn!(error = %e, "broadcast: failed to fetch miners"),
    }
}

async fn shutdown_signal() {
    let ctrl_c = async {
        signal::ctrl_c()
            .await
            .expect("failed to install Ctrl+C handler");
    };

    #[cfg(unix)]
    let terminate = async {
        signal::unix::signal(signal::unix::SignalKind::terminate())
            .expect("failed to install SIGTERM handler")
            .recv()
            .await;
    };

    #[cfg(not(unix))]
    let terminate = std::future::pending::<()>();

    tokio::select! {
        _ = ctrl_c     => info!("received Ctrl+C"),
        _ = terminate  => info!("received SIGTERM"),
    }
}
