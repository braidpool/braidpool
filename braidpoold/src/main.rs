use bitcoincore_rpc::{Auth, Client, RpcApi};
use std::error::Error;
use std::net::SocketAddr;
use tower_http::cors::{Any, CorsLayer};

mod api;

fn get_env(key: &str) -> Result<String, String> {
    std::env::var(key).map_err(|_| format!("Environment variable {} not set", key))
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    dotenv::dotenv().ok();

    env_logger::init();

    let bitcoind_url = get_env("BITCOIND_URL")?;
    let bitcoind_user = get_env("BITCOIND_USER")?;
    let bitcoind_pass = get_env("BITCOIND_PASS")?;

    let cmempool_url = get_env("CMEMPOOL_URL")?;
    let cmempool_user = get_env("CMEMPOOL_USER")?;
    let cmempool_pass = get_env("CMEMPOOL_PASS")?;

    let api_host = get_env("API_HOST").unwrap_or_else(|_| "127.0.0.1".to_string());
    let api_port = get_env("API_PORT")
        .unwrap_or_else(|_| "3001".to_string())
        .parse::<u16>()
        .unwrap_or(3001);

    // Orchestration check
    let standard = Client::new(&bitcoind_url, Auth::UserPass(bitcoind_user, bitcoind_pass))?;
    let committed = Client::new(&cmempool_url, Auth::UserPass(cmempool_user, cmempool_pass))?;

    println!("Standard node block count: {}", standard.get_block_count()?);
    println!(
        "Committed node block count: {}",
        committed.get_block_count()?
    );

    // API with CORS enabled
    let app = api::build_router().layer(
        CorsLayer::new()
            .allow_origin(Any)
            .allow_methods(Any)
            .allow_headers(Any),
    );

    // Start API server
    let addr = SocketAddr::from((
        api_host
            .parse::<std::net::IpAddr>()
            .unwrap_or([127, 0, 0, 1].into()),
        api_port,
    ));
    println!("API running at http://{}", addr);

    axum::serve(tokio::net::TcpListener::bind(addr).await?, app).await?;

    Ok(())
}
