use clap::Parser;
use std::error::Error;
use std::net::ToSocketAddrs;
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::mpsc;
use tokio_util::codec::{FramedRead, FramedWrite, LengthDelimitedCodec};

mod block_template;
mod cli;
mod connection;
mod protocol;
mod rpc;
mod zmq;

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    let args = cli::Cli::parse();

    setup_logging();
    setup_tracing()?;

    let datadir = args.datadir;
    log::info!("Using braid data directory: {}", datadir.display());

    let rpc = rpc::setup(
        args.bitcoin.clone(),
        args.rpcport,
        args.rpcuser,
        args.rpcpass,
    )?;
    let zmq_url = format!("tcp://{}:{}", args.bitcoin, args.zmqhashblockport);

    let (block_template_tx, block_template_rx) = mpsc::channel(1);
    tokio::spawn(zmq::zmq_hashblock_listener(zmq_url, rpc, block_template_tx));
    tokio::spawn(block_template::consumer(block_template_rx));

    if let Some(addnode) = args.addnode {
        for node in addnode.iter() {
            //log::info!("Connecting to node: {:?}", node);
            let stream = TcpStream::connect(node).await.expect("Error connecting");
            let (r, w) = stream.into_split();
            let framed_reader = FramedRead::new(r, LengthDelimitedCodec::new());
            let framed_writer = FramedWrite::new(w, LengthDelimitedCodec::new());
            let mut conn = connection::Connection::new(framed_reader, framed_writer);
            if let Ok(addr_iter) = node.to_socket_addrs() {
                if let Some(addr) = addr_iter.into_iter().next() {
                    tokio::spawn(async move {
                        if conn.start_from_connect(&addr).await.is_err() {
                            log::warn!("Peer {} closed connection", addr)
                        }
                    });
                }
            }
        }
    }

    log::info!("Binding to {}", args.bind);
    let listener = TcpListener::bind(&args.bind).await?;
    loop {
        // Asynchronously wait for an inbound TcpStream.
        log::info!("Starting accept");
        match listener.accept().await {
            Ok((stream, _)) => {
                let addr = stream.peer_addr()?;
                log::info!("Accepted connection from {}", addr);
                let (r, w) = stream.into_split();
                let framed_reader = FramedRead::new(r, LengthDelimitedCodec::new());
                let framed_writer = FramedWrite::new(w, LengthDelimitedCodec::new());
                let mut conn = connection::Connection::new(framed_reader, framed_writer);

                tokio::spawn(async move {
                    if conn.start_from_accept().await.is_err() {
                        log::warn!("Peer {} closed connection", addr)
                    }
                });
            }
            Err(e) => log::error!("couldn't get client: {:?}", e),
        }
    }
}

fn setup_logging() {
    env_logger::init_from_env(
        env_logger::Env::default().filter_or(env_logger::DEFAULT_FILTER_ENV, "info"),
    );
}

fn setup_tracing() -> Result<(), Box<dyn Error>> {
    // Create a filter for controlling the verbosity of tracing output
    let filter =
        tracing_subscriber::EnvFilter::from_default_env().add_directive("chat=info".parse()?);

    // Build a `tracing` subscriber with the specified filter
    let subscriber = tracing_subscriber::FmtSubscriber::builder()
        .with_env_filter(filter)
        .finish();

    // Set the subscriber as the global default for tracing
    tracing::subscriber::set_global_default(subscriber).expect("setting default subscriber failed");

    Ok(())
}
