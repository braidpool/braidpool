mod args;

use stratum_apps::config_helpers::logging::init_logging;
use translator_sv2::TranslatorSv2;

#[tokio::main]
async fn main() {
    let config = args::load_translator_config().unwrap_or_else(|e| {
        eprintln!("error: {e}");
        std::process::exit(1);
    });

    init_logging(config.log_dir());

    let translator = TranslatorSv2::new(config);

    tokio::spawn({
        let t = translator.clone();
        async move {
            if tokio::signal::ctrl_c().await.is_ok() {
                tracing::info!("Ctrl+C received, shutting down");
                t.shutdown().await;
            }
        }
    });

    if translator.start().await.is_err() {
        std::process::exit(1);
    }
}
