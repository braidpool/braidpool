use std::sync::Arc;

use axum::{
    routing::{delete, get, post, put},
    Router,
};
use sqlx::SqlitePool;
use tokio::sync::broadcast;
use tower_http::cors::{AllowHeaders, AllowMethods, AllowOrigin, CorsLayer};
use tower_http::trace::TraceLayer;

pub mod handlers;
pub mod models;

pub struct AppState {
    pub pool: SqlitePool,
    pub config: crate::config::Config,
    pub broadcast_tx: broadcast::Sender<String>,
}

pub fn build_router(state: Arc<AppState>) -> Router {
    let cors = build_cors(&state.config.cors_origins);

    Router::new()
        .route("/api/health", get(handlers::health))
        // Miner CRUD
        .route("/api/miners", post(handlers::add_miner))
        .route("/api/miners", get(handlers::get_all_miners))
        .route("/api/miners/:id", get(handlers::get_miner))
        // Debug: re-probe live, return raw + normalized side by side
        .route("/api/miners/:id/debug", get(handlers::debug_miner))
        .route("/api/miners/:id", put(handlers::update_miner))
        .route("/api/miners/:id", delete(handlers::delete_miner))
        // Refresh
        .route("/api/miners/:id/refresh", post(handlers::refresh_miner))
        .route(
            "/api/miners/refresh/all",
            post(handlers::refresh_all_miners),
        )
        // Scan
        .route("/api/miners/scan/lan", post(handlers::scan_lan))
        .route("/api/miners/scan/subnet", post(handlers::scan_subnet))
        // Real-time WebSocket — pushes miner list on every refresh/scan
        .route("/api/miners/ws", get(handlers::ws_miners))
        .layer(cors)
        .layer(TraceLayer::new_for_http())
        .with_state(state)
}

fn build_cors(origins: &[String]) -> CorsLayer {
    let allow: Vec<axum::http::HeaderValue> =
        origins.iter().filter_map(|o| o.parse().ok()).collect();

    CorsLayer::new()
        .allow_origin(AllowOrigin::list(allow))
        .allow_methods(AllowMethods::list([
            axum::http::Method::GET,
            axum::http::Method::POST,
            axum::http::Method::PUT,
            axum::http::Method::DELETE,
            axum::http::Method::OPTIONS,
        ]))
        .allow_headers(AllowHeaders::any())
}
