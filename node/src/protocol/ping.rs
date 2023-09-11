use super::{Message, ProtocolMessage};
use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize, PartialEq)]
pub struct PingMessage {
    pub message: String,
}

impl ProtocolMessage for PingMessage {
    fn start() -> Option<Message> {
        Some(Message::Ping(PingMessage {
            message: String::from("ping"),
        }))
    }

    fn response_for_received(&self) -> Result<Option<Message>, &'static str> {
        println!("Received {:?}", self.message);
        if self.message == "ping" {
            Ok(Some(Message::Ping(PingMessage {
                message: String::from("pong"),
            })))
        } else {
            Ok(None)
        }
    }
}
