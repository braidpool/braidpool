use std::error::Error;
use tokio::net::tcp::{OwnedReadHalf, OwnedWriteHalf};
use tokio::sync::mpsc;
use tokio_util::codec::{FramedRead, FramedWrite, LinesCodec};

const CHANNEL_CAPACITY: usize = 32;

pub async fn start_from_connect(
    reader: FramedRead<OwnedReadHalf, LinesCodec>,
    writer: FramedWrite<OwnedWriteHalf, LinesCodec>,
) -> Result<(), Box<dyn Error>> {
    println!("Starting from connect");
    let (channel_sender, channel_receiver) = mpsc::channel(CHANNEL_CAPACITY);
    start_read_loop(reader, channel_sender).await?;
    println!("read loop started in connect..");
    start_connect_protocols(writer, channel_receiver).await?;
    Ok(())
}

pub async fn start_from_accept(
    reader: FramedRead<OwnedReadHalf, LinesCodec>,
    writer: FramedWrite<OwnedWriteHalf, LinesCodec>,
) -> Result<(), Box<dyn Error>> {
    println!("Starting from accept");
    let (channel_sender, channel_receiver) = mpsc::channel(CHANNEL_CAPACITY);
    let _ = start_read_loop(reader, channel_sender).await;
    println!("read loop started in accept..");
    let _ = start_accept_protocols(writer, channel_receiver).await;
    Ok(())
}

pub async fn start_read_loop(
    mut reader: FramedRead<OwnedReadHalf, LinesCodec>,
    channel_sender: mpsc::Sender<String>,
) -> Result<(), Box<dyn Error>> {
    use futures::StreamExt;
    tokio::spawn(async move {
        println!("Start read loop....");
        loop {
            match reader.next().await {
                Some(item) => match item {
                    Ok(message) => {
                        println!("received {:?}", message);
                        let _ = channel_sender.send(message).await;
                    }
                    Err(_) => {
                        println!("Peer closed connection");
                        return;
                    }
                },
                None => {
                    println!("Peer closed connection");
                    return;
                }
            }
        }
    });
    Ok(())
}

async fn start_accept_protocols(
    mut writer: FramedWrite<OwnedWriteHalf, LinesCodec>,
    mut channel_receiver: mpsc::Receiver<String>,
) -> Result<(), Box<dyn Error>> {
    use futures::SinkExt;
    println!("Starting accept protocols......");
    tokio::spawn(async move {
        println!("Starting channel receiver...");
        while let Some(message) = channel_receiver.recv().await {
            println!("GOT = {:?}", message);
            let _ = writer.send(message).await;
        }
    });
    Ok(())
}

async fn start_connect_protocols(
    mut writer: FramedWrite<OwnedWriteHalf, LinesCodec>,
    mut channel_receiver: mpsc::Receiver<String>,
) -> Result<(), Box<dyn Error>> {
    use futures::SinkExt;
    writer.send("ping\n").await?;
    println!("Ping sent...");
    tokio::spawn(async move {
        while let Some(message) = channel_receiver.recv().await {
            println!("GOT = {:?}", message);
            let _ = writer.send(message).await;
        }
    });
    Ok(())
}
