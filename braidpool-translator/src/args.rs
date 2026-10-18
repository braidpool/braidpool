use clap::Parser;
use std::path::PathBuf;
use stratum_apps::config_helpers::load_config;
use translator_sv2::{config::TranslatorConfig, error::TproxyErrorKind};

#[derive(Parser, Debug)]
#[command(
    name = "braidpool-translator",
    about = "SV1-to-SV2 translator proxy for Braidpool"
)]
struct Args {
    /// Path to the TOML configuration file.
    #[arg(
        short = 'c',
        long = "config",
        default_value = "braidpool-translator.toml"
    )]
    config_path: PathBuf,

    /// Write logs to this file in addition to stdout.
    #[arg(short = 'f', long = "log-file")]
    log_file: Option<PathBuf>,
}

/// Array/list fields in [`TranslatorConfig`] that need special deserialization handling.
const LIST_KEYS: &[&str] = &[
    "supported_extensions",
    "required_extensions",
    "miner_telemetry.cidrs",
];

const ENUM_KEYS: &[&str] = &[];

/// Load [`TranslatorConfig`] from the TOML file at `--config`, with `BTPROXY__*`
/// environment variable overrides (e.g. `BTPROXY__DOWNSTREAM_PORT=3355`).
pub fn load_translator_config() -> Result<TranslatorConfig, TproxyErrorKind> {
    let args = Args::parse();
    let mut config: TranslatorConfig =
        load_config(&args.config_path, "BTPROXY", LIST_KEYS, ENUM_KEYS)?;
    config.set_log_dir(args.log_file);
    Ok(config)
}
