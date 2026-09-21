#[derive(Debug, Clone)]
pub struct Config {
    pub port: u16,
    pub db_path: String,
    pub cors_origins: Vec<String>,
    pub refresh_interval_secs: u64,
    pub scan_interval_secs: u64,
    pub miner_timeout_secs: u64,
    pub max_concurrent_probes: usize,
}

impl Default for Config {
    fn default() -> Self {
        Self {
            port: 5001,
            db_path: "miners.db".to_string(),
            cors_origins: vec![
                "http://localhost:3000".to_string(),
                "http://localhost:3001".to_string(),
            ],
            refresh_interval_secs: 1,
            scan_interval_secs: 300,
            miner_timeout_secs: 5,
            max_concurrent_probes: 256,
        }
    }
}

impl Config {
    pub fn from_env() -> Self {
        let mut cfg = Self::default();

        macro_rules! parse_env {
            ($var:literal, $field:expr, $ty:ty) => {
                if let Ok(v) = std::env::var($var) {
                    match v.parse::<$ty>() {
                        Ok(n) => $field = n,
                        Err(_) => tracing::warn!(
                            var = $var, value = %v, default = ?$field,
                            "invalid env value — using default"
                        ),
                    }
                }
            };
        }

        parse_env!("MINER_API_PORT", cfg.port, u16);
        parse_env!("MINER_REFRESH_INTERVAL", cfg.refresh_interval_secs, u64);
        parse_env!("MINER_SCAN_INTERVAL", cfg.scan_interval_secs, u64);
        parse_env!("MINER_TIMEOUT", cfg.miner_timeout_secs, u64);
        parse_env!("MINER_MAX_CONCURRENT", cfg.max_concurrent_probes, usize);

        if let Ok(v) = std::env::var("MINER_API_DB") {
            cfg.db_path = v;
        }
        if let Ok(v) = std::env::var("MINER_API_CORS_ORIGINS") {
            cfg.cors_origins = v.split(',').map(|s| s.trim().to_string()).collect();
        }
        cfg
    }
}
