use std::error::Error;
pub trait Protocol {
    fn start(&mut self) -> Option<&str>;
    fn received(&mut self, message: &str) -> Option<&str>;
}

pub struct Ping {}

impl Protocol for Ping {
    fn start(&mut self) -> Option<&str> {
        Some("ping")
    }

    fn received(&mut self, message: &str) -> Option<&str> {
        match message {
            "ping" => Some("pong"),
            _ => None,
        }
    }
}

pub fn get_protocol(message: &str) -> Result<Box<dyn Protocol>, Box<dyn Error>> {
    match message {
        "ping" => return Ok(Box::new(Ping {})),
        _ => Err("Unsupported protocol")?,
    }
}
