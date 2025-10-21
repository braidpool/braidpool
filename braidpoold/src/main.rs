use bitcoincore_rpc::{Auth, Client, RpcApi};
use std::error::Error;
use std::net::SocketAddr;
use tower_http::cors::{Any, CorsLayer};

mod api;

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    env_logger::init();

    // Orchestration check
    let standard = Client::new(
        "http://127.0.0.1:18332",
        Auth::UserPass("jevinrpc".to_string(), "securepass123".to_string()),
    )?;
    let committed = Client::new(
        "http://127.0.0.1:19443",
        Auth::UserPass("cmempoolrpc".to_string(), "securepass456".to_string()),
    )?;

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
    let addr = SocketAddr::from(([127, 0, 0, 1], 3000));
    println!("API running at http://{}", addr);

    axum::serve(tokio::net::TcpListener::bind(addr).await?, app).await?;

    Ok(())
}
