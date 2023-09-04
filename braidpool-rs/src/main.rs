use std::env;
use std::error::Error;
// use std::sync::Arc;
// use tokio::io::AsyncWriteExt;
use tokio::net::{TcpListener, TcpStream};

mod connection;

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    setup_tracing()?;

    let seed_addr = env::args().nth(1).unwrap();
    let addr = env::args().nth(2).unwrap();

    // Connect to seed node, if found, else continue
    if seed_addr != addr {
        let stream = TcpStream::connect(seed_addr).await?;
        // let peer_connection = connection::build_connection(stream);
        let (reader, mut writer) = stream.into_split();
        let _ = connection::start_from_connect(reader, &mut writer).await;
    }

    let listener = TcpListener::bind(&addr).await?;
    loop {
        // Asynchronously wait for an inbound TcpStream.
        let (stream, _peer_addr) = listener.accept().await.expect("Error accepting");

        tracing::debug!("accepted connection");
        // let peer_connection = connection::build_connection(stream);
        let (reader, mut writer) = stream.into_split();
        let _ = connection::start_from_accept(reader, &mut writer).await;
    }
}

fn setup_tracing() -> Result<(), Box<dyn Error>> {
    use tracing_subscriber::{fmt::format::FmtSpan, EnvFilter};
    // Configure a `tracing` subscriber that logs traces emitted by the chat
    // server.
    tracing_subscriber::fmt()
        // Filter what traces are displayed based on the RUST_LOG environment
        // variable.
        //
        // Traces emitted by the example code will always be displayed. You
        // can set `RUST_LOG=tokio=trace` to enable additional traces emitted by
        // Tokio itself.
        .with_env_filter(EnvFilter::from_default_env().add_directive("chat=info".parse()?))
        // Log events when `tracing` spans are created, entered, exited, or
        // closed. When Tokio's internal tracing support is enabled (as
        // described above), this can be used to track the lifecycle of spawned
        // tasks on the Tokio runtime.
        .with_span_events(FmtSpan::FULL)
        // Set this subscriber as the default, to collect all traces emitted by
        // the program.
        .init();
    Ok(())
}
