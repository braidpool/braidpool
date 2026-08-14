use chrono::Utc;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use sqlx::FromRow;

#[derive(Debug, Clone, FromRow, Serialize, Deserialize)]
pub struct MinerDevice {
    pub id: String,
    pub ip: String,
    pub name: Option<String>,

    // Device identification
    pub hostname: Option<String>,
    pub mac: Option<String>,
    pub make: Option<String>,
    pub model: Option<String>,
    pub firmware: Option<String>,

    // Performance metrics
    pub hashrate_current: Option<f64>,
    pub hashrate_avg: Option<f64>,
    pub expected_hashrate: Option<f64>,

    // Temperature readings
    pub temperature: Option<f64>,
    pub temperature_max: Option<f64>,
    pub vr_temperature: Option<f64>,

    // Power metrics
    pub power_usage: Option<i64>,
    pub power_limit: Option<i64>,
    pub efficiency: Option<f64>,
    pub voltage: Option<f64>,

    // Hardware status (stored as JSON strings in SQLite)
    pub fan_speeds: String,
    pub chip_count: Option<i64>,
    pub is_mining: Option<bool>,
    pub errors: String,
    pub uptime: Option<i64>,

    // Pool information (stored as JSON string)
    pub pools: String,
    pub primary_pool: String,

    // API info
    pub api_version: Option<String>,

    // Connection status
    pub is_online: bool,
    pub last_error: Option<String>,

    // Timestamps
    pub created_at: String,
    pub updated_at: String,
    pub last_seen: Option<String>,
}

impl MinerDevice {
    pub fn to_json(&self) -> Value {
        let fan_speeds: Value =
            serde_json::from_str(&self.fan_speeds).unwrap_or(Value::Array(vec![]));
        let errors: Value = serde_json::from_str(&self.errors).unwrap_or(Value::Array(vec![]));
        let pools: Value = serde_json::from_str(&self.pools).unwrap_or(Value::Array(vec![]));

        serde_json::json!({
            "id":               self.id,
            "ip":               self.ip,
            "name":             self.name,
            "hostname":         self.hostname,
            "mac":              self.mac,
            "make":             self.make,
            "model":            self.model,
            "firmware":         self.firmware,
            "hashrate_current": self.hashrate_current,
            "hashrate_avg":     self.hashrate_avg,
            "expected_hashrate":self.expected_hashrate,
            "temperature":      self.temperature,
            "temperature_max":  self.temperature_max,
            "vr_temperature":   self.vr_temperature,
            "power_usage":      self.power_usage,
            "power_limit":      self.power_limit,
            "efficiency":       self.efficiency,
            "voltage":          self.voltage,
            "fan_speeds":       fan_speeds,
            "chip_count":       self.chip_count,
            "is_mining":        self.is_mining,
            "errors":           errors,
            "uptime":           self.uptime,
            "pools":            pools,
            "primary_pool":     self.primary_pool,
            "api_version":      self.api_version,
            "is_online":        self.is_online,
            "last_error":       self.last_error,
            "created_at":       self.created_at,
            "updated_at":       self.updated_at,
            "last_seen":        self.last_seen,
        })
    }

    pub fn now_iso() -> String {
        Utc::now().format("%Y-%m-%dT%H:%M:%SZ").to_string()
    }
}
