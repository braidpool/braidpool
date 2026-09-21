use serde::{Deserialize, Serialize};

//  request models

#[derive(Debug, Deserialize)]
pub struct AddMinerRequest {
    pub ip: String,
    pub name: Option<String>,
}

#[derive(Debug, Deserialize)]
pub struct UpdateMinerRequest {
    pub name: Option<String>,
}

#[derive(Debug, Deserialize)]
pub struct ScanSubnetRequest {
    pub cidr: String,
}

//  response models

#[derive(Debug, Serialize)]
pub struct HealthResponse {
    pub status: &'static str,
    pub version: &'static str,
    pub timestamp: String,
}

#[derive(Debug, Serialize)]
pub struct ScanResponse {
    pub found: usize,
    pub added: usize,
    pub skipped: usize,
}

/// Validate and parse an IP address string; returns an error string on failure.
pub fn parse_ip(s: &str) -> Result<std::net::IpAddr, String> {
    s.trim()
        .parse()
        .map_err(|_| format!("invalid IP address: {s}"))
}
