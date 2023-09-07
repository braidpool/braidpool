use std::env;
use std::error::Error;
use tokio::net::{TcpListener, TcpStream};
use tokio_util::codec::{FramedRead, FramedWrite, LinesCodec};

mod connection;
mod protocol;

#[tokio::main]
async fn main() -> Result<(), Box<dyn Error>> {
    setup_tracing()?;

    let seed_addr = env::args().nth(1).unwrap();
    let addr = env::args().nth(2).unwrap();

    // Connect to seed node, if found, else continue
    if seed_addr != addr {
        let stream = TcpStream::connect(seed_addr)
            .await
            .expect("Error connecting");
        let (r, w) = stream.into_split();
        let framed_reader = FramedRead::new(r, LinesCodec::new());
        let framed_writer = FramedWrite::new(w, LinesCodec::new());
        let mut conn = connection::Connection::new(framed_reader, framed_writer);
        tokio::spawn(async move {
            match conn.start_from_connect().await {
                Err(_) => {
                    println!("peer closed connection");
                    return;
                }
                Ok(_) => {}
            }
        });
    }

    let listener = TcpListener::bind(&addr).await?;
    loop {
        // Asynchronously wait for an inbound TcpStream.
        println!("Starting accept");
        match listener.accept().await {
            Ok((stream, _)) => {
                println!("\n\naccepted connection");
                let (r, w) = stream.into_split();
                let framed_reader = FramedRead::new(r, LinesCodec::new());
                let framed_writer = FramedWrite::new(w, LinesCodec::new());
                let mut conn = connection::Connection::new(framed_reader, framed_writer);

                tokio::spawn(async move {
                    match conn.start_from_accept().await {
                        Err(e) => {
                            println!("Connection shutdown: {:?}", e);
                            return;
                        }
                        Ok(_) => {}
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
