use std::time::Duration;

use sqlx::SqlitePool;
use tracing::{info, warn};
use uuid::Uuid;

use crate::db::service;

const POLL_INTERVAL: Duration = Duration::from_secs(5);
const STATS_TIMEOUT: Duration = Duration::from_secs(4);
// Ports probed automatically on startup for CPU miners running locally.
const DEFAULT_PORTS: &[u16] = &[8080, 8081, 8082];

/// Normalizes an api_url so `localhost` and `127.0.0.1` compare as equal.
pub fn normalize_api_url(url: &str) -> String {
    url.trim_end_matches('/').replace("localhost", "127.0.0.1")
}

pub fn validate_api_url(url: &str) -> Result<(), &'static str> {
    let parsed = reqwest::Url::parse(url).map_err(|_| "api_url must be a valid URL")?;
    if parsed.scheme() != "http" && parsed.scheme() != "https" {
        return Err("api_url must use http or https");
    }
    if !parsed.username().is_empty() || parsed.password().is_some() {
        return Err("api_url must not contain credentials");
    }
    if parsed.query().is_some() || parsed.fragment().is_some() {
        return Err("api_url must not contain a query or fragment");
    }

    match parsed.host_str() {
        Some("localhost") | Some("127.0.0.1") | Some("::1") => Ok(()),
        _ => Err("api_url must point to localhost"),
    }
}

fn is_valid_stats(body: &str) -> bool {
    let Ok(value) = serde_json::from_str::<serde_json::Value>(body) else {
        return false;
    };
    let Some(object) = value.as_object() else {
        return false;
    };
    object.get("minerVersion").is_some()
        && object
            .get("uptimeSeconds")
            .and_then(|v| v.as_u64())
            .is_some()
        && object
            .get("hashrate")
            .and_then(|v| v.get("currentKhashS"))
            .and_then(|v| v.as_f64())
            .is_some()
        && object.get("shares").and_then(|v| v.as_object()).is_some()
        && object
            .get("connection")
            .and_then(|v| v.as_object())
            .is_some()
        && object
            .get("workerThreads")
            .and_then(|v| v.as_array())
            .is_some()
        && object
            .get("recentShares")
            .and_then(|v| v.as_array())
            .is_some()
}

pub struct CpuMinerService {
    pool: SqlitePool,
    http: reqwest::Client,
}

impl CpuMinerService {
    pub fn new(pool: SqlitePool) -> Self {
        let http = reqwest::Client::builder()
            .timeout(STATS_TIMEOUT)
            .build()
            .expect("reqwest client");
        Self { pool, http }
    }

    pub fn start(self) -> tokio::task::JoinHandle<()> {
        tokio::spawn(async move { self.run().await })
    }

    async fn run(self) {
        info!("cpu miner poller started");
        self.auto_discover().await;
        let mut interval = tokio::time::interval(POLL_INTERVAL);
        interval.set_missed_tick_behavior(tokio::time::MissedTickBehavior::Skip);
        loop {
            interval.tick().await;
            self.auto_discover().await;
            self.poll_all().await;
        }
    }

    /// Probe well-known localhost ports and register any live CPU miners not yet in the DB.
    async fn auto_discover(&self) {
        for &port in DEFAULT_PORTS {
            let url = format!("http://127.0.0.1:{}/api/v1/health", port);
            if self
                .http
                .get(&url)
                .send()
                .await
                .map(|r| r.status().is_success())
                .unwrap_or(false)
            {
                let api_url = format!("http://127.0.0.1:{}", port);
                let existing = service::cpu_miner_list(&self.pool)
                    .await
                    .unwrap_or_default();
                // Compare on normalized host (localhost == 127.0.0.1) so a miner
                // registered under either form isn't auto-discovered as a duplicate.
                if existing
                    .iter()
                    .any(|m| normalize_api_url(&m.api_url) == normalize_api_url(&api_url))
                {
                    continue;
                }
                let id = Uuid::new_v4().to_string();
                match service::cpu_miner_insert(&self.pool, &id, &api_url, Some("Local CPU Miner"))
                    .await
                {
                    Ok(_) => info!(port, "auto-registered cpu miner"),
                    Err(e) => warn!(port, error = %e, "auto-register failed"),
                }
            }
        }
    }

    async fn poll_all(&self) {
        let miners = match service::cpu_miner_list(&self.pool).await {
            Ok(m) => m,
            Err(e) => {
                warn!(error = %e, "cpu miner poll: failed to list miners");
                return;
            }
        };

        for miner in miners {
            let url = format!("{}/api/v1/stats", miner.api_url.trim_end_matches('/'));
            match self.http.get(&url).send().await {
                Ok(resp) if resp.status().is_success() => match resp.text().await {
                    Ok(body) if is_valid_stats(&body) => {
                        if let Err(e) = service::cpu_miner_update_stats(
                            &self.pool,
                            &miner.id,
                            true,
                            Some(&body),
                        )
                        .await
                        {
                            warn!(id = %miner.id, error = %e, "cpu miner poll: update failed");
                        }
                    }
                    Ok(_) => {
                        warn!(id = %miner.id, "cpu miner poll: non-JSON response");
                        let _ = service::cpu_miner_update_stats(&self.pool, &miner.id, false, None)
                            .await;
                    }
                    Err(e) => {
                        warn!(id = %miner.id, error = %e, "cpu miner poll: read body failed");
                        let _ = service::cpu_miner_update_stats(&self.pool, &miner.id, false, None)
                            .await;
                    }
                },
                Ok(resp) => {
                    warn!(id = %miner.id, status = %resp.status(), "cpu miner poll: non-2xx");
                    let _ =
                        service::cpu_miner_update_stats(&self.pool, &miner.id, false, None).await;
                }
                Err(e) => {
                    warn!(id = %miner.id, error = %e, "cpu miner poll: unreachable");
                    let _ =
                        service::cpu_miner_update_stats(&self.pool, &miner.id, false, None).await;
                }
            }
        }
    }
}
