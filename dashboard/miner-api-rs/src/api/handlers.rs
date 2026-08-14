use asic_rs::core::data::hashrate::HashRateUnit;
use asic_rs::MinerFactory;
use axum::{
    extract::{
        ws::{Message, WebSocket, WebSocketUpgrade},
        Path, State,
    },
    http::StatusCode,
    response::IntoResponse,
    Json,
};
use serde_json::Value;
use std::sync::Arc;
use std::time::Duration;
use tokio::sync::{broadcast, Semaphore};
use tracing::warn;

use crate::api::models::{
    AddMinerRequest, HealthResponse, ScanResponse, ScanSubnetRequest, UpdateMinerRequest,
};
use crate::api::AppState;
use crate::db::{models::MinerDevice, service};
use crate::miner_service;
use crate::scanner;

const VERSION: &str = env!("CARGO_PKG_VERSION");

pub async fn ws_miners(
    ws: WebSocketUpgrade,
    State(state): State<Arc<AppState>>,
) -> impl IntoResponse {
    ws.on_upgrade(move |socket| handle_ws(socket, state))
}

async fn handle_ws(mut socket: WebSocket, state: Arc<AppState>) {
    if let Ok(miners) = service::get_all(&state.pool).await {
        let list: Vec<Value> = miners.iter().map(|m| m.to_json()).collect();
        let msg = serde_json::to_string(&serde_json::json!({
            "success": true,
            "miners":  list,
        }))
        .unwrap_or_default();
        if socket.send(Message::Text(msg)).await.is_err() {
            return;
        }
    }

    // Then stream every broadcast the background tasks fire.
    let mut rx: broadcast::Receiver<String> = state.broadcast_tx.subscribe();
    loop {
        tokio::select! {
            result = rx.recv() => {
                match result {
                    Ok(msg) => {
                        if socket.send(Message::Text(msg)).await.is_err() {
                            break; // client disconnected
                        }
                    }
                    Err(broadcast::error::RecvError::Lagged(_)) => continue, // skip stale
                    Err(_) => break,
                }
            }
            // Drain incoming frames (pings, close frames) without blocking.
            msg = socket.recv() => {
                match msg {
                    Some(Ok(Message::Close(_))) | None => break,
                    _ => {}
                }
            }
        }
    }
}

pub async fn health() -> Json<HealthResponse> {
    Json(HealthResponse {
        status: "healthy",
        version: VERSION,
        timestamp: MinerDevice::now_iso(),
    })
}

pub async fn add_miner(
    State(state): State<Arc<AppState>>,
    Json(req): Json<AddMinerRequest>,
) -> impl IntoResponse {
    let ip = match crate::api::models::parse_ip(&req.ip) {
        Ok(ip) => ip,
        Err(e) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(serde_json::json!({ "success": false, "error": e })),
            )
        }
    };

    match service::add_miner(&state.pool, ip, req.name, state.config.miner_timeout_secs).await {
        Ok(v) => {
            let already = v["already_exists"].as_bool().unwrap_or(false);
            let code = if already {
                StatusCode::CONFLICT
            } else {
                StatusCode::OK
            };
            (code, Json(v))
        }
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "success": false, "error": e.to_string() })),
        ),
    }
}

pub async fn get_all_miners(State(state): State<Arc<AppState>>) -> impl IntoResponse {
    match service::get_all(&state.pool).await {
        Ok(miners) => {
            let list: Vec<Value> = miners.iter().map(|m| m.to_json()).collect();
            (
                StatusCode::OK,
                Json(serde_json::json!({
                    "success": true,
                    "count":   list.len(),
                    "miners":  list,
                })),
            )
        }
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "success": false, "error": e.to_string() })),
        ),
    }
}

pub async fn debug_miner(
    State(state): State<Arc<AppState>>,
    Path(id): Path<String>,
) -> impl IntoResponse {
    let device = match service::get_by_id(&state.pool, &id).await {
        Ok(Some(d)) => d,
        Ok(None) => {
            return (
                StatusCode::NOT_FOUND,
                Json(serde_json::json!({ "error": "Miner not found" })),
            )
        }
        Err(e) => {
            return (
                StatusCode::INTERNAL_SERVER_ERROR,
                Json(serde_json::json!({ "error": e.to_string() })),
            )
        }
    };

    let ip: std::net::IpAddr = match device.ip.parse() {
        Ok(ip) => ip,
        Err(_) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(serde_json::json!({ "error": "Bad IP in DB" })),
            )
        }
    };

    let timeout = Duration::from_secs(state.config.miner_timeout_secs);
    let factory = MinerFactory::new();

    let miner = match tokio::time::timeout(timeout, factory.get_miner(ip)).await {
        Ok(Ok(Some(m))) => m,
        Ok(Ok(None)) => {
            return (
                StatusCode::OK,
                Json(serde_json::json!({ "error": "No miner detected at this IP" })),
            )
        }
        Ok(Err(e)) => {
            return (
                StatusCode::OK,
                Json(serde_json::json!({ "error": format!("Probe failed: {e}") })),
            )
        }
        Err(_) => {
            return (
                StatusCode::OK,
                Json(serde_json::json!({ "error": "Probe timed out" })),
            )
        }
    };

    let info = miner.get_device_info();

    let raw_data = match tokio::time::timeout(timeout, miner.get_data()).await {
        Ok(d) => d,
        Err(_) => {
            return (
                StatusCode::OK,
                Json(serde_json::json!({
                    "ip":    ip.to_string(),
                    "make":  info.make,
                    "model": info.model,
                    "error": "get_data() timed out — only device info available",
                })),
            )
        }
    };
    let hashboards: Vec<Value> = raw_data.hashboards.iter().map(|b| {
        serde_json::json!({
            "position": b.position,
            "outlet_temperature_C":  b.outlet_temperature.map(|t| t.as_celsius()),
            "intake_temperature_C":  b.intake_temperature.map(|t| t.as_celsius()),
            "board_temperature_C":   b.board_temperature.map(|t| t.as_celsius()),
            "hashrate_TH":           b.hashrate.as_ref().map(|h| h.clone().as_unit(HashRateUnit::TeraHash).value),
            "expected_hashrate_TH":  b.expected_hashrate.as_ref().map(|h| h.clone().as_unit(HashRateUnit::TeraHash).value),
            "working_chips":         b.working_chips,
            "expected_chips":        b.expected_chips,
            "voltage_V":             b.voltage.map(|v| v.as_volts()),
        })
    }).collect();

    let fans: Vec<Value> = raw_data
        .fans
        .iter()
        .chain(raw_data.psu_fans.iter())
        .map(|f| {
            serde_json::json!({
                "position": f.position,
                "rpm":      f.rpm.map(|r| r.as_rpm().round() as i64),
            })
        })
        .collect();

    let pools_raw: Vec<Value> = raw_data
        .pools
        .iter()
        .flat_map(|g| {
            g.pools.iter().map(|p| {
                serde_json::json!({
                    "url":    p.url.as_ref().map(|u| u.to_string()),
                    "user":   p.user,
                    "active": p.active,
                    "alive":  p.alive,
                })
            })
        })
        .collect();

    let raw_hostname = raw_data.hostname.clone();
    let raw_firmware = raw_data.firmware_version.clone();
    let raw_is_mining = raw_data.is_mining;
    let raw_uptime_s = raw_data.uptime.map(|d| d.as_secs());
    let raw_hashrate_th = raw_data
        .hashrate
        .as_ref()
        .map(|h| h.clone().as_unit(HashRateUnit::TeraHash).value);
    let raw_expected_th = raw_data
        .expected_hashrate
        .as_ref()
        .map(|h| h.clone().as_unit(HashRateUnit::TeraHash).value);
    let raw_wattage_w = raw_data.wattage.map(|w| w.as_watts());
    let raw_efficiency = raw_data.efficiency; // raw firmware value, unit unspecified
    let raw_avg_temp_c = raw_data.average_temperature.map(|t| t.as_celsius());
    let raw_fluid_temp_c = raw_data.fluid_temperature.map(|t| t.as_celsius());
    let raw_total_chips = raw_data.total_chips;

    let normalized = miner_service::normalize(raw_data);

    let debug = serde_json::json!({
        "raw": {
            "ip":                    ip.to_string(),
            "make":                  info.make,
            "model":                 info.model,
            "hostname":              raw_hostname,
            "firmware":              raw_firmware,
            "is_mining":             raw_is_mining,
            "uptime_s":              raw_uptime_s,
            "hashrate_TH":           raw_hashrate_th,
            "expected_hashrate_TH":  raw_expected_th,
            "wattage_W":             raw_wattage_w,
            "efficiency_raw":        raw_efficiency,
            "average_temperature_C": raw_avg_temp_c,
            "fluid_temperature_C":   raw_fluid_temp_c,
            "total_chips":           raw_total_chips,
            "hashboards":            hashboards,
            "fans":                  fans,
            "pools":                 pools_raw,
        },
        "normalized": {
            "hashrate_current_TH":  normalized.hashrate_current,
            "expected_hashrate_TH": normalized.expected_hashrate,
            "temperature_C":        normalized.temperature,
            "temperature_max_C":    normalized.temperature_max,
            "vr_temperature_C":     normalized.vr_temperature,
            "power_usage_W":        normalized.power_usage,
            "efficiency_J_per_TH":  normalized.efficiency,
            "fan_speeds_rpm":       normalized.fan_speeds,
            "is_mining":            normalized.is_mining,
            "primary_pool":         normalized.primary_pool,
        },
    });

    (StatusCode::OK, Json(debug))
}

pub async fn get_miner(
    State(state): State<Arc<AppState>>,
    Path(id): Path<String>,
) -> impl IntoResponse {
    match service::get_by_id(&state.pool, &id).await {
        Ok(Some(m)) => (
            StatusCode::OK,
            Json(serde_json::json!({ "success": true, "miner": m.to_json() })),
        ),
        Ok(None) => (
            StatusCode::NOT_FOUND,
            Json(serde_json::json!({ "success": false, "error": "Miner not found" })),
        ),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "success": false, "error": e.to_string() })),
        ),
    }
}

pub async fn update_miner(
    State(state): State<Arc<AppState>>,
    Path(id): Path<String>,
    Json(req): Json<UpdateMinerRequest>,
) -> impl IntoResponse {
    match service::update_name(&state.pool, &id, req.name).await {
        Ok(v) => {
            let not_found = v["not_found"].as_bool().unwrap_or(false);
            let code = if not_found {
                StatusCode::NOT_FOUND
            } else {
                StatusCode::OK
            };
            (code, Json(v))
        }
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "success": false, "error": e.to_string() })),
        ),
    }
}

pub async fn delete_miner(
    State(state): State<Arc<AppState>>,
    Path(id): Path<String>,
) -> impl IntoResponse {
    match service::delete(&state.pool, &id).await {
        Ok(v) => {
            let not_found = v["not_found"].as_bool().unwrap_or(false);
            let code = if not_found {
                StatusCode::NOT_FOUND
            } else {
                StatusCode::OK
            };
            (code, Json(v))
        }
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "success": false, "error": e.to_string() })),
        ),
    }
}

pub async fn refresh_miner(
    State(state): State<Arc<AppState>>,
    Path(id): Path<String>,
) -> impl IntoResponse {
    match service::refresh_one(&state.pool, &id, state.config.miner_timeout_secs).await {
        Ok(v) => {
            let not_found = v["not_found"].as_bool().unwrap_or(false);
            let code = if not_found {
                StatusCode::NOT_FOUND
            } else {
                StatusCode::OK
            };
            (code, Json(v))
        }
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "success": false, "error": e.to_string() })),
        ),
    }
}

pub async fn refresh_all_miners(State(state): State<Arc<AppState>>) -> impl IntoResponse {
    match service::refresh_all(
        &state.pool,
        state.config.miner_timeout_secs,
        state.config.max_concurrent_probes,
    )
    .await
    {
        Ok(s) => (
            StatusCode::OK,
            Json(serde_json::json!({
                "total":   s.total,
                "success": s.success,
                "failed":  s.failed,
                "miners":  s.miners,
            })),
        ),
        Err(e) => (
            StatusCode::INTERNAL_SERVER_ERROR,
            Json(serde_json::json!({ "success": false, "error": e.to_string() })),
        ),
    }
}

async fn persist_scan_results(
    miners: &[Box<dyn asic_rs::core::traits::miner::Miner>],
    state: &Arc<AppState>,
) -> ScanResponse {
    let found = miners.len();
    let timeout = state.config.miner_timeout_secs;
    let concurrency = state.config.max_concurrent_probes.max(1);
    let pool = state.pool.clone();
    let sem = Arc::new(Semaphore::new(concurrency));
    let futs: Vec<_> = miners
        .iter()
        .map(|miner| {
            let ip = miner.get_ip();
            let pool = pool.clone();
            let sem = Arc::clone(&sem);
            async move {
                let _permit = sem
                    .acquire_owned()
                    .await
                    .expect("semaphore should not be closed during scan");
                let data = miner_service::normalize_handle(miner.as_ref(), timeout).await;
                (ip, service::upsert_discovered(&pool, ip, &data).await)
            }
        })
        .collect();

    let results = futures::future::join_all(futs).await;

    let mut added = 0usize;
    let mut skipped = 0usize;
    for (ip, result) in &results {
        match result {
            Ok(true) => added += 1,
            Ok(false) => skipped += 1,
            Err(e) => warn!(ip = %ip, error = %e, "upsert failed"),
        }
    }

    ScanResponse {
        found,
        added,
        skipped,
    }
}

pub async fn scan_lan(State(state): State<Arc<AppState>>) -> impl IntoResponse {
    let miners = scanner::scan_lan().await;
    let summary = persist_scan_results(&miners, &state).await;
    (StatusCode::OK, Json(serde_json::json!(summary)))
}

pub async fn scan_subnet(
    State(state): State<Arc<AppState>>,
    Json(req): Json<ScanSubnetRequest>,
) -> impl IntoResponse {
    let miners = match scanner::scan_subnet(&req.cidr).await {
        Ok(m) => m,
        Err(e) => {
            return (
                StatusCode::BAD_REQUEST,
                Json(serde_json::json!({ "success": false, "error": e.to_string() })),
            )
        }
    };

    let summary = persist_scan_results(&miners, &state).await;
    (StatusCode::OK, Json(serde_json::json!(summary)))
}
