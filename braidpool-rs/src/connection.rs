use std::error::Error;
use tokio::net::tcp::{OwnedReadHalf, OwnedWriteHalf};
use tokio::sync::mpsc;
use tokio_util::codec::{FramedRead, FramedWrite, LinesCodec};

const CHANNEL_CAPACITY: usize = 32;

pub struct Connection {
    reader: FramedRead<OwnedReadHalf, LinesCodec>,
    writer: FramedWrite<OwnedWriteHalf, LinesCodec>,
    //channel_receiver: mpsc::Receiver<String>,
    //channel_sender: mpsc::Sender<String>,
}

impl Connection {
    pub fn new(
        reader: FramedRead<OwnedReadHalf, LinesCodec>,
        writer: FramedWrite<OwnedWriteHalf, LinesCodec>,
    ) -> Connection {
        //let (channel_sender, channel_receiver) = mpsc::channel(CHANNEL_CAPACITY);
        Connection {
            reader,
            writer,
            // channel_receiver,
            // channel_sender,
        }
    }

    pub async fn start_from_connect(&mut self) -> Result<(), Box<dyn Error>> {
        use futures::SinkExt;
        println!("Starting from connect");
        self.writer.send("ping").await?;
        self.start_read_loop().await?;
        Ok(())
    }

    pub async fn start_from_accept(&mut self) -> Result<(), Box<dyn Error>> {
        println!("Starting from accept");
        self.start_read_loop().await?;
        Ok(())
    }

    pub async fn start_read_loop(&mut self) -> Result<(), Box<dyn Error>> {
        use futures::SinkExt;
        use futures::StreamExt;
        println!("Start read loop....");
        loop {
            match self.reader.next().await {
                None => {
                    return Err("peer closed connection".into());
                }
                Some(item) => {
                    println!("Started {:?}", item);
                    match item {
                        Err(_) => {
                            return Err("peer closed connection".into());
                        }
                        Ok(message) => {
                            println!("Started {:?}", message);
                            if message == "ping" {
                                self.writer.send("pong").await?;
                            }
                        }
                    }
                }
            }
        }
    }
}
