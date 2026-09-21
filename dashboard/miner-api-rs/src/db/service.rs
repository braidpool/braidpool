use anyhow::{anyhow, Result};
use serde_json::Value;
use sqlx::SqlitePool;
use std::net::IpAddr;
use std::sync::Arc;
use tokio::sync::Semaphore;
use tracing::{info, warn};
use uuid::Uuid;

use crate::db::models::MinerDevice;
use crate::miner_service::{self, NormalizedMinerData};

fn json_str(v: &[Value]) -> String {
    serde_json::to_string(v).unwrap_or_else(|_| "[]".to_string())
}

fn pools_to_json(pools: &[crate::miner_service::PoolInfo]) -> String {
    let values: Vec<Value> = pools
        .iter()
        .map(|p| {
            serde_json::json!({
                "url":    p.url,
                "user":   p.user,
                "status": p.status,
            })
        })
        .collect();
    serde_json::to_string(&values).unwrap_or_else(|_| "[]".to_string())
}

fn new_device(id: &str, ip: &str, name: Option<String>, now: &str) -> MinerDevice {
    MinerDevice {
        id: id.to_string(),
        ip: ip.to_string(),
        name,
        fan_speeds: "[]".into(),
        errors: "[]".into(),
        pools: "[]".into(),
        primary_pool: "No Pool".into(),
        is_online: false,
        last_error: None,
        created_at: now.to_string(),
        updated_at: now.to_string(),
        last_seen: None,
        hostname: None,
        mac: None,
        make: None,
        model: None,
        firmware: None,
        hashrate_current: None,
        hashrate_avg: None,
        expected_hashrate: None,
        temperature: None,
        temperature_max: None,
        vr_temperature: None,
        power_usage: None,
        power_limit: None,
        efficiency: None,
        voltage: None,
        chip_count: None,
        is_mining: None,
        uptime: None,
        api_version: None,
    }
}

fn apply_normalized(device: &mut MinerDevice, data: &NormalizedMinerData) {
    device.hostname = data.hostname.clone();
    device.mac = data.mac.clone();
    device.make = data.make.clone();
    device.model = data.model.clone();
    device.firmware = data.firmware.clone();
    device.hashrate_current = data.hashrate_current;
    device.hashrate_avg = data.hashrate_avg;
    device.expected_hashrate = data.expected_hashrate;
    device.temperature = data.temperature;
    device.temperature_max = data.temperature_max;
    device.vr_temperature = data.vr_temperature;
    device.power_usage = data.power_usage;
    device.power_limit = data.power_limit;
    device.efficiency = data.efficiency;
    device.voltage = data.voltage;
    device.fan_speeds = json_str(
        &data
            .fan_speeds
            .iter()
            .map(|&s: &i64| Value::Number(s.into()))
            .collect::<Vec<_>>(),
    );
    device.chip_count = data.chip_count;
    device.is_mining = Some(data.is_mining);
    device.errors = json_str(
        &data
            .errors
            .iter()
            .map(|e: &String| Value::String(e.clone()))
            .collect::<Vec<_>>(),
    );
    device.uptime = data.uptime;
    device.pools = pools_to_json(&data.pools);
    device.primary_pool = data.primary_pool.clone();
    device.api_version = data.api_version.clone();
    device.is_online = true;
    device.last_error = None;
    // Use a single timestamp so last_seen and updated_at are identical.
    let now = MinerDevice::now_iso();
    device.last_seen = Some(now.clone());
    device.updated_at = now;
}

/// Typed outcome of probing a miner — eliminates JSON field inspection at call sites.
pub enum ProbeResult {
    Online(MinerDevice),
    Offline { device: MinerDevice, error: String },
}

/// Write the full telemetry UPDATE for one miner row.
/// Used by both `do_refresh` (success path) and `upsert_discovered`.
/// Schema changes only need to be applied here.
async fn update_telemetry(pool: &SqlitePool, device: &MinerDevice) -> Result<()> {
    sqlx::query(
        r#"UPDATE miner_devices SET
            hostname=?, mac=?, make=?, model=?, firmware=?,
            hashrate_current=?, hashrate_avg=?, expected_hashrate=?,
            temperature=?, temperature_max=?, vr_temperature=?,
            power_usage=?, power_limit=?, efficiency=?, voltage=?,
            fan_speeds=?, chip_count=?, is_mining=?, errors=?, uptime=?,
            pools=?, primary_pool=?, api_version=?,
            is_online=1, last_error=NULL, updated_at=?, last_seen=?
        WHERE id=?"#,
    )
    .bind(&device.hostname)
    .bind(&device.mac)
    .bind(&device.make)
    .bind(&device.model)
    .bind(&device.firmware)
    .bind(device.hashrate_current)
    .bind(device.hashrate_avg)
    .bind(device.expected_hashrate)
    .bind(device.temperature)
    .bind(device.temperature_max)
    .bind(device.vr_temperature)
    .bind(device.power_usage)
    .bind(device.power_limit)
    .bind(device.efficiency)
    .bind(device.voltage)
    .bind(&device.fan_speeds)
    .bind(device.chip_count)
    .bind(device.is_mining)
    .bind(&device.errors)
    .bind(device.uptime)
    .bind(&device.pools)
    .bind(&device.primary_pool)
    .bind(&device.api_version)
    .bind(&device.updated_at)
    .bind(&device.last_seen)
    .bind(&device.id)
    .execute(pool)
    .await?;
    Ok(())
}

pub async fn add_miner(
    pool: &SqlitePool,
    ip: IpAddr,
    name: Option<String>,
    timeout_secs: u64,
) -> Result<Value> {
    let ip_str = ip.to_string();
    let id = Uuid::new_v4().to_string();
    let now = MinerDevice::now_iso();
    let rows = sqlx::query(
        r#"INSERT OR IGNORE INTO miner_devices
           (id, ip, name, is_online, created_at, updated_at)
           VALUES (?, ?, ?, 0, ?, ?)"#,
    )
    .bind(&id)
    .bind(&ip_str)
    .bind(&name)
    .bind(&now)
    .bind(&now)
    .execute(pool)
    .await?
    .rows_affected();

    if rows == 0 {
        let existing = get_by_ip(pool, &ip_str)
            .await?
            .ok_or_else(|| anyhow!("duplicate IP but row not found"))?;
        return Ok(serde_json::json!({
            "success":        false,
            "error":          format!("Miner with IP {ip_str} already exists"),
            "already_exists": true,
            "miner":          existing.to_json(),
        }));
    }
    let device = new_device(&id, &ip_str, name, &now);
    match do_refresh(pool, device, timeout_secs).await? {
        ProbeResult::Online(m) => {
            info!(ip = %ip_str, model = ?m.model, "miner added online");
            Ok(serde_json::json!({ "success": true, "miner": m.to_json() }))
        }
        ProbeResult::Offline { device: m, .. } => {
            warn!(ip = %ip_str, "miner added as offline");
            Ok(serde_json::json!({
                "success": true,
                "warning": "Miner added but currently offline",
                "miner":   m.to_json(),
            }))
        }
    }
}

pub async fn get_by_id(pool: &SqlitePool, id: &str) -> Result<Option<MinerDevice>> {
    Ok(
        sqlx::query_as::<_, MinerDevice>("SELECT * FROM miner_devices WHERE id = ?")
            .bind(id)
            .fetch_optional(pool)
            .await?,
    )
}

pub async fn get_by_ip(pool: &SqlitePool, ip: &str) -> Result<Option<MinerDevice>> {
    Ok(
        sqlx::query_as::<_, MinerDevice>("SELECT * FROM miner_devices WHERE ip = ?")
            .bind(ip)
            .fetch_optional(pool)
            .await?,
    )
}

pub async fn get_all(pool: &SqlitePool) -> Result<Vec<MinerDevice>> {
    Ok(
        sqlx::query_as::<_, MinerDevice>("SELECT * FROM miner_devices ORDER BY created_at DESC")
            .fetch_all(pool)
            .await?,
    )
}

pub async fn update_name(pool: &SqlitePool, id: &str, name: Option<String>) -> Result<Value> {
    let now = MinerDevice::now_iso();
    let rows = sqlx::query("UPDATE miner_devices SET name = ?, updated_at = ? WHERE id = ?")
        .bind(&name)
        .bind(&now)
        .bind(id)
        .execute(pool)
        .await?
        .rows_affected();

    if rows == 0 {
        return Ok(
            serde_json::json!({ "success": false, "error": "Miner not found", "not_found": true }),
        );
    }
    let device = get_by_id(pool, id)
        .await?
        .ok_or_else(|| anyhow!("row disappeared after update"))?;
    Ok(serde_json::json!({ "success": true, "miner": device.to_json() }))
}

pub async fn delete(pool: &SqlitePool, id: &str) -> Result<Value> {
    let rows = sqlx::query("DELETE FROM miner_devices WHERE id = ?")
        .bind(id)
        .execute(pool)
        .await?
        .rows_affected();

    if rows == 0 {
        return Ok(
            serde_json::json!({ "success": false, "error": "Miner not found", "not_found": true }),
        );
    }
    Ok(serde_json::json!({ "success": true }))
}
async fn do_refresh(
    pool: &SqlitePool,
    device: MinerDevice,
    timeout_secs: u64,
) -> Result<ProbeResult> {
    let ip: IpAddr = device.ip.parse()?;
    let id = device.id.clone();
    let now = MinerDevice::now_iso();

    match miner_service::probe_ip(ip, timeout_secs).await {
        Some(data) => {
            let mut d = device;
            apply_normalized(&mut d, &data);
            update_telemetry(pool, &d).await?;
            let updated = get_by_id(pool, &id)
                .await?
                .ok_or_else(|| anyhow!("row lost"))?;
            Ok(ProbeResult::Online(updated))
        }
        None => {
            let error = format!("Miner did not respond within {timeout_secs}s");
            sqlx::query(
                "UPDATE miner_devices SET is_online=0, last_error=?, updated_at=? WHERE id=?",
            )
            .bind(&error)
            .bind(&now)
            .bind(&id)
            .execute(pool)
            .await?;
            let updated = get_by_id(pool, &id)
                .await?
                .ok_or_else(|| anyhow!("row lost"))?;
            Ok(ProbeResult::Offline {
                device: updated,
                error,
            })
        }
    }
}

pub async fn refresh_one(pool: &SqlitePool, id: &str, timeout_secs: u64) -> Result<Value> {
    let device = match get_by_id(pool, id).await? {
        Some(d) => d,
        None => {
            return Ok(serde_json::json!({
                "success":   false,
                "error":     "Miner not found",
                "not_found": true,
            }))
        }
    };
    match do_refresh(pool, device, timeout_secs).await? {
        ProbeResult::Online(m) => Ok(serde_json::json!({ "success": true, "miner": m.to_json() })),
        ProbeResult::Offline { device: m, error } => {
            Ok(serde_json::json!({ "success": false, "error": error, "miner": m.to_json() }))
        }
    }
}

pub struct RefreshSummary {
    pub total: usize,
    pub success: usize,
    pub failed: usize,
    pub miners: Vec<Value>,
}

pub async fn refresh_all(
    pool: &SqlitePool,
    timeout_secs: u64,
    max_concurrent: usize,
) -> Result<RefreshSummary> {
    let devices = get_all(pool).await?;
    let total = devices.len();
    let mut success = 0usize;
    let mut failed = 0usize;
    let mut results: Vec<Value> = Vec::with_capacity(total);

    // Limit concurrent probes to avoid overwhelming the network.
    let sem = Arc::new(Semaphore::new(max_concurrent.max(1)));
    let handles: Vec<_> = devices
        .into_iter()
        .map(|d| {
            let pool = pool.clone();
            let sem = Arc::clone(&sem);
            tokio::spawn(async move {
                let _permit = sem
                    .acquire_owned()
                    .await
                    .map_err(|_| anyhow!("semaphore closed"))?;
                match do_refresh(&pool, d, timeout_secs).await {
                    Ok(ProbeResult::Online(m)) =>
                        Ok(serde_json::json!({ "success": true, "miner": m.to_json() })),
                    Ok(ProbeResult::Offline { device: m, error }) =>
                        Ok(serde_json::json!({ "success": false, "error": error, "miner": m.to_json() })),
                    Err(e) => Err(e),
                }
            })
        })
        .collect();

    for handle in handles {
        match handle.await {
            Ok(Ok(v)) => {
                let ok = v["success"].as_bool().unwrap_or(false);
                let miner = v["miner"].clone();
                if ok {
                    success += 1;
                } else {
                    failed += 1;
                }
                results.push(serde_json::json!({ "success": ok, "miner": miner }));
            }
            Ok(Err(e)) => {
                failed += 1;
                results.push(serde_json::json!({ "success": false, "error": e.to_string() }));
            }
            Err(e) => {
                failed += 1;
                results.push(serde_json::json!({ "success": false, "error": e.to_string() }));
            }
        }
    }

    Ok(RefreshSummary {
        total,
        success,
        failed,
        miners: results,
    })
}
pub async fn upsert_discovered(
    pool: &SqlitePool,
    ip: IpAddr,
    data: &NormalizedMinerData,
) -> Result<bool> {
    let ip_str = ip.to_string();
    let id = Uuid::new_v4().to_string();
    let now = MinerDevice::now_iso();
    let rows = sqlx::query(
        r#"INSERT OR IGNORE INTO miner_devices
           (id, ip, is_online, created_at, updated_at)
           VALUES (?, ?, 0, ?, ?)"#,
    )
    .bind(&id)
    .bind(&ip_str)
    .bind(&now)
    .bind(&now)
    .execute(pool)
    .await?
    .rows_affected();

    if rows == 0 {
        return Ok(false);
    }
    let mut device = new_device(&id, &ip_str, None, &now);
    apply_normalized(&mut device, data);
    update_telemetry(pool, &device).await?;

    info!(ip = %ip_str, "discovered miner added");
    Ok(true)
}
