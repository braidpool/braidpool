use bytes::Bytes;
use std::{error::Error, net::SocketAddr};
use tokio::net::tcp::{OwnedReadHalf, OwnedWriteHalf};
//use tokio::sync::mpsc;
use tokio_util::codec::{FramedRead, FramedWrite, LengthDelimitedCodec};

// const CHANNEL_CAPACITY: usize = 32;

use crate::error::ProtocolError;
use crate::protocol::{self, HandshakeMessage, Message, ProtocolMessage};

pub struct Connection {
    reader: FramedRead<OwnedReadHalf, LengthDelimitedCodec>,
    writer: FramedWrite<OwnedWriteHalf, LengthDelimitedCodec>,
    //channel_receiver: mpsc::Receiver<String>,
    //channel_sender: mpsc::Sender<String>,
}

impl Connection {
    pub fn new(
        reader: FramedRead<OwnedReadHalf, LengthDelimitedCodec>,
        writer: FramedWrite<OwnedWriteHalf, LengthDelimitedCodec>,
    ) -> Connection {
        //let (channel_sender, channel_receiver) = mpsc::channel(CHANNEL_CAPACITY);
        Connection {
            reader,
            writer,
            // channel_receiver,
            // channel_sender,
        }
    }

    pub async fn start_from_connect(&mut self, addr: &SocketAddr) -> Result<(), Box<dyn Error>> {
        use futures::SinkExt;
        log::info!("Starting from connect");
        let message = HandshakeMessage::start(addr).ok_or(ProtocolError::MessageCreation)?;
        self.writer.send(message.as_bytes()?).await?;
        self.start_read_loop().await?;
        Ok(())
    }

    pub async fn start_from_accept(&mut self) -> Result<(), Box<dyn Error>> {
        log::info!("Starting from accept");
        self.start_read_loop().await?;
        Ok(())
    }

    pub async fn start_read_loop(&mut self) -> Result<(), Box<dyn Error>> {
        use futures::StreamExt;
        log::info!("Start read loop....");
        loop {
            match self.reader.next().await {
                None => {
                    return Err("peer closed connection".into());
                }
                Some(item) => match item {
                    Err(_) => {
                        return Err("peer closed connection".into());
                    }
                    Ok(message) => {
                        if self.message_received(&message.freeze()).await.is_err() {
                            return Err("peer closed connection".into());
                        }
                    }
                },
            }
        }
    }

    async fn message_received(&mut self, message: &Bytes) -> Result<(), &'static str> {
        use futures::SinkExt;

        let message: Message = protocol::Message::from_bytes(message)
            .map_err(|_| "Error deserializing: Closing peer connection")?;
        match message.response_for_received() {
            Ok(result) => {
                if let Some(response) = result {
                    match response.as_bytes() {
                        Ok(to_send) => {
                            if (self.writer.send(to_send).await).is_err() {
                                return Err("Send failed: Closing peer connection");
                            }
                        }
                        Err(_) => {
                            return Err("Error serializing: Closing peer connection");
                        }
                    }
                }
            }
            Err(_) => {
                return Err("Error constructing response: Closing peer connection");
            }
        }
        Ok(())
    }
}
