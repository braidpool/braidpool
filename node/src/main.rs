use clap::Parser;
use std::error::Error;
use std::net::ToSocketAddrs;
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::mpsc;
use tokio_util::codec::{FramedRead, FramedWrite, LengthDelimitedCodec};

mod cli;
mod connection;
mod protocol;
mod block_template;

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    let args = cli::Cli::parse();

    let datadir = args.datadir;
    println!("Using braid data directory: {}", datadir.display());

    setup_tracing()?;

    let (block_template_tx, block_template_rx) = mpsc::channel(1);
    tokio::spawn(block_template::poll(
        args.rpc_url,
        args.rpc_user,
        args.rpc_pass,
        args.poll_interval,
        block_template_tx,
    ));
    tokio::spawn(block_template::consumer(block_template_rx));

    if let Some(addnode) = args.addnode {
        for node in addnode.iter() {
            //println!("Connecting to node: {:?}", node);
            let stream = TcpStream::connect(node).await.expect("Error connecting");
            let (r, w) = stream.into_split();
            let framed_reader = FramedRead::new(r, LengthDelimitedCodec::new());
            let framed_writer = FramedWrite::new(w, LengthDelimitedCodec::new());
            let mut conn = connection::Connection::new(framed_reader, framed_writer);
            if let Ok(addr_iter) = node.to_socket_addrs() {
                if let Some(addr) = addr_iter.into_iter().next() {
                    tokio::spawn(async move {
                        if conn.start_from_connect(&addr).await.is_err() {
                            println!("Peer closed connection")
                        }
                    });
                }
            }
        }
    }

    println!("Binding to {}", args.bind);
    let listener = TcpListener::bind(&args.bind).await?;
    loop {
        // Asynchronously wait for an inbound TcpStream.
        println!("Starting accept");
        match listener.accept().await {
            Ok((stream, _)) => {
                println!("\n\naccepted connection");
                let (r, w) = stream.into_split();
                let framed_reader = FramedRead::new(r, LengthDelimitedCodec::new());
                let framed_writer = FramedWrite::new(w, LengthDelimitedCodec::new());
                let mut conn = connection::Connection::new(framed_reader, framed_writer);

                tokio::spawn(async move {
                    if conn.start_from_accept().await.is_err() {
                        println!("Peer closed connection")
                    }
                });
            }
            Err(e) => println!("couldn't get client: {:?}", e),
        }
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
