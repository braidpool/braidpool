use std::net::IpAddr;
use std::time::Duration;

use asic_rs::core::data::hashrate::HashRateUnit;
use asic_rs::MinerFactory;
use tracing::{debug, warn};

/// pool info
#[derive(Debug, Clone)]
pub struct PoolInfo {
    pub url: Option<String>,
    pub user: Option<String>,
    pub status: Option<String>,
}

#[derive(Debug, Clone)]
pub struct NormalizedMinerData {
    pub hostname: Option<String>,
    pub mac: Option<String>,
    pub make: Option<String>,
    pub model: Option<String>,
    pub firmware: Option<String>,

    pub hashrate_current: Option<f64>,
    pub hashrate_avg: Option<f64>,
    pub expected_hashrate: Option<f64>,

    pub temperature: Option<f64>,
    pub temperature_max: Option<f64>,
    pub vr_temperature: Option<f64>,

    pub power_usage: Option<i64>,
    pub power_limit: Option<i64>,
    pub efficiency: Option<f64>,
    pub voltage: Option<f64>,

    pub fan_speeds: Vec<i64>,
    pub chip_count: Option<i64>,
    pub is_mining: bool,
    pub errors: Vec<String>,
    pub uptime: Option<i64>,

    pub pools: Vec<PoolInfo>,
    pub primary_pool: String,
    pub api_version: Option<String>,
}
fn offline_from_make_model(make: &str, model: &str, reason: &str) -> NormalizedMinerData {
    NormalizedMinerData {
        hostname: None,
        mac: None,
        make: Some(make.to_string()),
        model: Some(model.to_string()),
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
        fan_speeds: vec![],
        chip_count: None,
        is_mining: false,
        errors: vec![reason.to_string()],
        uptime: None,
        pools: vec![],
        primary_pool: "No Pool".to_string(),
        api_version: None,
    }
}

pub async fn normalize_handle(
    miner: &dyn asic_rs::core::traits::miner::Miner,
    timeout_secs: u64,
) -> NormalizedMinerData {
    let timeout = Duration::from_secs(timeout_secs);
    let info = miner.get_device_info();

    match tokio::time::timeout(timeout, miner.get_data()).await {
        Ok(data) => normalize(data),
        Err(_) => {
            warn!(ip = %miner.get_ip(), "get_data timed out, storing device info only");
            offline_from_make_model(&info.make, &info.model, "get_data timed out")
        }
    }
}
pub async fn probe_ip(ip: IpAddr, timeout_secs: u64) -> Option<NormalizedMinerData> {
    let factory = MinerFactory::new();
    let timeout = Duration::from_secs(timeout_secs);

    let miner = match tokio::time::timeout(timeout, factory.get_miner(ip)).await {
        Ok(Ok(Some(m))) => m,
        Ok(Ok(None)) => {
            debug!(ip = %ip, "no miner detected");
            return None;
        }
        Ok(Err(e)) => {
            warn!(ip = %ip, error = %e, "probe error");
            return None;
        }
        Err(_) => {
            warn!(ip = %ip, "probe timed out");
            return None;
        }
    };

    let data = match tokio::time::timeout(timeout, miner.get_data()).await {
        Ok(d) => d,
        Err(_) => {
            warn!(ip = %ip, "get_data timed out, using device_info only");
            let info = miner.get_device_info();
            return Some(offline_from_make_model(
                &info.make,
                &info.model,
                "get_data timed out",
            ));
        }
    };

    Some(normalize(data))
}
pub fn normalize(data: asic_rs::core::data::miner::MinerData) -> NormalizedMinerData {
    //  hashrate
    let hashrate_current = data
        .hashrate
        .map(|h| round2(h.as_unit(HashRateUnit::TeraHash).value));
    let expected_hashrate = data
        .expected_hashrate
        .map(|h| round2(h.as_unit(HashRateUnit::TeraHash).value));

    //  temperatures
    let outlet_temps: Vec<f64> = data
        .hashboards
        .iter()
        .filter_map(|b| b.outlet_temperature.map(|t| t.as_celsius()))
        .collect();

    let intake_temps: Vec<f64> = data
        .hashboards
        .iter()
        .filter_map(|b| b.intake_temperature.map(|t| t.as_celsius()))
        .collect();

    // temperature_max
    let temperature_max = outlet_temps
        .iter()
        .cloned()
        .reduce(f64::max)
        .map(round2)
        .or_else(|| intake_temps.iter().cloned().reduce(f64::max).map(round2));
    let temperature = data
        .average_temperature
        .map(|t| round2(t.as_celsius()))
        .or(temperature_max);
    let board_temps: Vec<f64> = data
        .hashboards
        .iter()
        .filter_map(|b| b.board_temperature.map(|t| t.as_celsius()))
        .collect();

    let vr_temperature = board_temps
        .iter()
        .cloned()
        .reduce(f64::max)
        .map(round2)
        .or_else(|| data.fluid_temperature.map(|t| round2(t.as_celsius())));

    // power
    let power_usage = data.wattage.map(|w| w.as_watts().round() as i64);
    let efficiency = data.efficiency.map(round2).or_else(|| {
        if let (Some(p), Some(h)) = (power_usage, hashrate_current) {
            if h > 0.0 {
                Some(round2(p as f64 / h))
            } else {
                None
            }
        } else {
            None
        }
    });

    //  fans
    let fan_speeds: Vec<i64> = data
        .fans
        .iter()
        .chain(data.psu_fans.iter())
        .filter_map(|f| f.rpm.map(|r| r.as_rpm().round() as i64))
        .collect();

    //  pools
    let pools: Vec<PoolInfo> = data
        .pools
        .iter()
        .flat_map(|group| {
            group.pools.iter().map(|p| {
                let status = match (p.active, p.alive) {
                    (Some(true), _) => Some("active".to_string()),
                    (_, Some(true)) => Some("alive".to_string()),
                    (Some(false), _) => Some("inactive".to_string()),
                    _ => None,
                };
                PoolInfo {
                    url: p.url.as_ref().map(|u| u.to_string()),
                    user: p.user.clone(),
                    status,
                }
            })
        })
        .collect();

    let primary_pool = extract_primary_pool_name(&pools);

    //  errors
    let errors: Vec<String> = data.messages.iter().map(|m| format!("{m:?}")).collect();

    //  misc
    let mac = data.mac.as_ref().map(|m| m.to_string());
    let uptime = data.uptime.map(|d| d.as_secs() as i64);
    let chip_count = data.total_chips.map(|c| c as i64);

    NormalizedMinerData {
        hostname: data.hostname,
        mac,
        make: Some(data.device_info.make.clone()),
        model: Some(data.device_info.model.clone()),
        firmware: data.firmware_version,
        hashrate_current,
        hashrate_avg: hashrate_current,
        expected_hashrate,
        temperature,
        temperature_max,
        vr_temperature,
        power_usage,
        power_limit: None,
        efficiency,
        voltage: None,
        fan_speeds,
        chip_count,
        is_mining: data.is_mining,
        errors,
        uptime,
        pools,
        primary_pool,
        api_version: data.api_version,
    }
}

fn round2(v: f64) -> f64 {
    (v * 100.0).round() / 100.0
}

fn extract_primary_pool_name(pools: &[PoolInfo]) -> String {
    let valid: Vec<&PoolInfo> = pools
        .iter()
        .filter(|p| p.url.is_some() && p.status.as_deref() != Some("inactive"))
        .collect();

    let url = match valid.first().and_then(|p| p.url.as_deref()) {
        Some(u) => u,
        None => return "No Pool".to_string(),
    };

    let full = if url.starts_with("stratum") || url.starts_with("http") {
        url.to_string()
    } else {
        format!("stratum+tcp://{url}")
    };
    let without_scheme = full.split("://").nth(1).unwrap_or(&full);
    let host_port = without_scheme.split('/').next().unwrap_or(without_scheme);
    let host = host_port.split(':').next().unwrap_or(host_port);

    if host.is_empty() {
        return "Unknown Pool".to_string();
    }

    let parts: Vec<&str> = host.split('.').collect();
    let name_part = if parts.len() >= 2 {
        parts[parts.len() - 2]
    } else {
        parts[0]
    };

    let mut chars = name_part.chars();
    match chars.next() {
        None => "Unknown Pool".to_string(),
        Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
    }
}
