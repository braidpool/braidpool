use clap::Parser;
use std::error::Error;
use std::fs;
use std::net::ToSocketAddrs;
use tokio::net::{TcpListener, TcpStream};
use tokio::sync::mpsc;
use tokio_util::codec::{FramedRead, FramedWrite, LengthDelimitedCodec};

mod block_template;
mod cli;
mod connection;
mod protocol;
mod rpc;
mod shutdown;
mod zmq;

use shutdown::ShutdownHandler;

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    let args = cli::Cli::parse();

    setup_logging();
    setup_tracing()?;

    let datadir = shellexpand::full(args.datadir.to_str().unwrap()).unwrap();
    match fs::metadata(&*datadir) {
        Ok(m) => {
            if !m.is_dir() {
                log::error!("Data directory {} exists but is not a directory", datadir);
            }
            log::info!("Using existing data directory: {}", datadir);
        }
        Err(_) => {
            log::info!("Creating data directory: {}", datadir);
            fs::create_dir_all(&*datadir)?;
        }
    }

    // Create shutdown handler
    let (shutdown_handler, _shutdown_rx) = ShutdownHandler::new();
    let shutdown_handler_clone = shutdown_handler.clone();

    // Setup RPC with error handling
    let rpc = match rpc::setup(
        args.bitcoin.clone(),
        args.rpcport,
        args.rpcuser,
        args.rpcpass,
        args.rpccookie,
    ) {
        Ok(rpc) => rpc,
        Err(e) => {
            shutdown_handler.shutdown_bitcoin_error(format!("Failed to setup Bitcoin RPC: {}", e));
            return Err(e.into());
        }
    };

    let zmq_url = format!("tcp://{}:{}", args.bitcoin, args.zmqhashblockport);

    let (block_template_tx, block_template_rx) = mpsc::channel(1);
    tokio::spawn(zmq::zmq_hashblock_listener(zmq_url, rpc, block_template_tx));
    tokio::spawn(block_template::consumer(block_template_rx));

    if let Some(addnode) = args.addnode {
        for node in addnode.iter() {
            let stream = match TcpStream::connect(node).await {
                Ok(stream) => stream,
                Err(e) => {
                    shutdown_handler.shutdown_connection_error(format!("Error connecting to {}: {}", node, e));
                    return Err(e.into());
                }
            };
            
            let (r, w) = stream.into_split();
            let framed_reader = FramedRead::new(r, LengthDelimitedCodec::new());
            let framed_writer = FramedWrite::new(w, LengthDelimitedCodec::new());
            let mut conn = connection::Connection::new(framed_reader, framed_writer);
            
            if let Ok(addr_iter) = node.to_socket_addrs() {
                if let Some(addr) = addr_iter.into_iter().next() {
                    let shutdown_handler = shutdown_handler_clone.clone();
                    tokio::spawn(async move {
                        if let Err(e) = conn.start_from_connect(&addr).await {
                            shutdown_handler.shutdown_connection_error(format!("Peer {} error: {}", addr, e));
                        }
                    });
                }
            }
        }
    }

    log::info!("Binding to {}", args.bind);
    let listener = match TcpListener::bind(&args.bind).await {
        Ok(listener) => listener,
        Err(e) => {
            shutdown_handler.shutdown_connection_error(format!("Failed to bind to {}: {}", args.bind, e));
            return Err(e.into());
        }
    };

    loop {
        log::info!("Starting accept");
        match listener.accept().await {
            Ok((stream, addr)) => {
                log::info!("Accepted connection from {}", addr);
                let (r, w) = stream.into_split();
                let framed_reader = FramedRead::new(r, LengthDelimitedCodec::new());
                let framed_writer = FramedWrite::new(w, LengthDelimitedCodec::new());
                let mut conn = connection::Connection::new(framed_reader, framed_writer);
                let shutdown_handler = shutdown_handler_clone.clone();

                tokio::spawn(async move {
                    if let Err(e) = conn.start_from_accept().await {
                        shutdown_handler.shutdown_connection_error(format!("Peer {} error: {}", addr, e));
                    }
                });
            }
            Err(e) => {
                shutdown_handler.shutdown_connection_error(format!("Accept error: {}", e));
                return Err(e.into());
            }
        }
    }
}

fn setup_logging() {
    env_logger::init_from_env(
        env_logger::Env::default().filter_or(env_logger::DEFAULT_FILTER_ENV, "info"),
    );
}

fn setup_tracing() -> Result<(), Box<dyn Error>> {
    let filter =
        tracing_subscriber::EnvFilter::from_default_env().add_directive("chat=info".parse()?);

    let subscriber = tracing_subscriber::FmtSubscriber::builder()
        .with_env_filter(filter)
        .finish();

    tracing::subscriber::set_global_default(subscriber).expect("setting default subscriber failed");

    Ok(())
}
