use bytes::Bytes;
use std::error::Error;
extern crate flexbuffers;
extern crate serde;
// #[macro_use]
// extern crate serde_derive;
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize, PartialEq)]
pub struct PingMessage {
    pub message: String,
}

#[derive(Debug, Serialize, Deserialize, PartialEq)]
pub enum Message {
    Ping(PingMessage),
}

pub trait Protocol {
    fn start(&self) -> Option<Message>;
    fn response_for_received(&self) -> Option<Bytes>;
}

impl Message {
    pub fn as_bytes(&self) -> Option<Bytes> {
        let mut s = flexbuffers::FlexbufferSerializer::new();
        self.serialize(&mut s).unwrap();
        Some(Bytes::from(s.take_buffer()))
    }
}

pub fn deserialize_message(b: &[u8]) -> Result<Message, Box<dyn Error>> {
    Ok(flexbuffers::from_slice(b)?)
}

impl Protocol for Message {
    fn start(&self) -> Option<Message> {
        Some(Message::Ping(PingMessage {
            message: String::from("ping"),
        }))
    }

    fn response_for_received(&self) -> Option<Bytes> {
        match self {
            Message::Ping(received) => {
                println!("Received {:?}", received.message);
                if received.message == "ping" {
                    let response = Message::Ping(PingMessage {
                        message: String::from("pong"),
                    });
                    let mut s = flexbuffers::FlexbufferSerializer::new();
                    response.serialize(&mut s).unwrap();
                    Some(Bytes::from(s.take_buffer()))
                } else {
                    None
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Message;
    use super::PingMessage;
    use crate::protocol::serde::Serialize;
    use bytes::Bytes;

    #[test]
    fn it_serialized_ping_message() {
        let ping_message = Message::Ping(PingMessage {
            message: String::from("ping"),
        });
        let mut s = flexbuffers::FlexbufferSerializer::new();
        ping_message.serialize(&mut s).unwrap();
        let b = Bytes::from(s.take_buffer());

        let m: Message = flexbuffers::from_slice(&b).unwrap();
        assert_eq!(m, ping_message);

        use super::Protocol;
        let x = m.start().unwrap();
        assert_eq!(
            x,
            Message::Ping(PingMessage {
                message: String::from("ping")
            })
        );
    }
}
