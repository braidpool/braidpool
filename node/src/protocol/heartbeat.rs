use super::{Message, ProtocolMessage};
use serde::{Deserialize, Serialize};
use std::{net::SocketAddr, time::SystemTime};

#[derive(Debug, Serialize, Deserialize, PartialEq)]
pub struct HeartbeatMessage {
    pub from: String,
    pub time: SystemTime,
}

impl ProtocolMessage for HeartbeatMessage {
    fn start(addr: &SocketAddr) -> Option<Message> {
        Some(Message::Heartbeat(HeartbeatMessage {
            from: addr.to_string(),
            time: SystemTime::now(),
        }))
    }

    fn response_for_received(&self) -> Result<Option<Message>, &'static str> {
        log::info!("Received {:?}", self);
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use std::net::SocketAddr;
    use std::str::FromStr;

    use crate::protocol::{HeartbeatMessage, Message, ProtocolMessage};

    #[test]
    fn it_matches_start_message_for_handshake() {
        let addr = SocketAddr::from_str("127.0.0.1:25188").unwrap();
        if let Some(Message::Heartbeat(start_message)) = HeartbeatMessage::start(&addr) {
            assert_eq!(start_message.from, String::from("127.0.0.1:25188"))
        }
    }

    #[test]
    fn it_matches_response_message_for_correct_handshake_start() {
        let addr = SocketAddr::from_str("127.0.0.1:25188").unwrap();
        let start_message = HeartbeatMessage::start(&addr).unwrap();
        let response = start_message.response_for_received().unwrap();
        assert_eq!(response, None);
    }
}
