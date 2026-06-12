//! Custom timestamp type for microseconds since epoch

use bitcoin::consensus::encode::Decodable;
use bitcoin::consensus::encode::Encodable;
use bitcoin::io::{self, BufRead, Write};
use serde::Deserialize;
use serde::Serialize;
use std::time::SystemTime;
use std::time::UNIX_EPOCH;

/// A timestamp representing microseconds since the Unix epoch
#[repr(transparent)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct MicrosecondTimestamp(u64);

impl MicrosecondTimestamp {
    /// Create a new timestamp from microseconds since epoch
    pub fn from_micros(micros: u64) -> Self {
        Self(micros)
    }

    /// Get the timestamp as microseconds since epoch
    pub fn as_micros(self) -> u64 {
        self.0
    }

    /// Get the timestamp as seconds since epoch (truncated)
    pub fn as_secs(self) -> u32 {
        (self.0 / 1_000_000) as u32
    }

    /// Get the timestamp as seconds since epoch (truncated) - method for compatibility
    pub fn to_u32(self) -> u32 {
        self.as_secs()
    }

    /// Create a timestamp from seconds since epoch
    pub fn from_secs(secs: u32) -> Self {
        Self(secs as u64 * 1_000_000)
    }

    /// Get the current timestamp
    pub fn now() -> Self {
        let micros = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_micros() as u64;
        Self(micros)
    }

    /// Convert to SystemTime
    pub fn to_system_time(self) -> SystemTime {
        UNIX_EPOCH + std::time::Duration::from_micros(self.0 as u64)
    }

    /// Convert from SystemTime
    pub fn from_system_time(time: SystemTime) -> Result<Self, std::time::SystemTimeError> {
        let micros = time.duration_since(UNIX_EPOCH)?.as_micros() as u64;
        Ok(Self(micros))
    }
}

impl Default for MicrosecondTimestamp {
    fn default() -> Self {
        Self::from_secs(0) // Unix epoch
    }
}

impl From<u64> for MicrosecondTimestamp {
    fn from(micros: u64) -> Self {
        Self(micros)
    }
}

impl From<MicrosecondTimestamp> for u64 {
    fn from(timestamp: MicrosecondTimestamp) -> Self {
        timestamp.0
    }
}

impl From<MicrosecondTimestamp> for i64 {
    fn from(timestamp: MicrosecondTimestamp) -> Self {
        timestamp.0 as i64
    }
}

impl From<u32> for MicrosecondTimestamp {
    fn from(secs: u32) -> Self {
        Self::from_secs(secs)
    }
}

impl From<MicrosecondTimestamp> for u32 {
    fn from(timestamp: MicrosecondTimestamp) -> Self {
        timestamp.as_secs()
    }
}

impl From<SystemTime> for MicrosecondTimestamp {
    fn from(time: SystemTime) -> Self {
        Self::from_system_time(time).expect("SystemTime should be after Unix epoch")
    }
}

impl From<MicrosecondTimestamp> for SystemTime {
    fn from(timestamp: MicrosecondTimestamp) -> Self {
        timestamp.to_system_time()
    }
}

// Consensus encoding support
impl Encodable for MicrosecondTimestamp {
    fn consensus_encode<W: Write + ?Sized>(&self, w: &mut W) -> Result<usize, io::Error> {
        self.0.consensus_encode(w)
    }
}

impl Decodable for MicrosecondTimestamp {
    fn consensus_decode<R: BufRead + ?Sized>(r: &mut R) -> Result<Self, bitcoin::consensus::Error> {
        let value = u64::consensus_decode(r)?;
        Ok(value.into())
    }
}

// Display formatting
impl std::fmt::Display for MicrosecondTimestamp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}μs", self.0)
    }
}

// Utility functions for common conversions
pub fn secs_to_micros(secs: u32) -> u64 {
    secs as u64 * 1_000_000
}

pub fn micros_to_secs(micros: u64) -> u32 {
    (micros / 1_000_000) as u32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_microsecond_timestamp_basic() {
        let timestamp = MicrosecondTimestamp::from_micros(1_653_195_600_000_000);
        assert_eq!(timestamp.as_micros(), 1_653_195_600_000_000);
        assert_eq!(timestamp.as_secs(), 1653195600);
    }

    #[test]
    fn test_from_secs() {
        let timestamp = MicrosecondTimestamp::from_secs(1653195600);
        assert_eq!(timestamp.as_micros(), 1_653_195_600_000_000);
        assert_eq!(timestamp.as_secs(), 1653195600);
    }

    #[test]
    fn test_conversions() {
        let original_micros: u64 = 1_653_195_600_123_456;
        let timestamp = MicrosecondTimestamp::from_micros(original_micros);

        assert_eq!(u64::from(timestamp), original_micros);
        assert_eq!(u32::from(timestamp), 1653195600);
    }

    #[test]
    fn test_now() {
        let timestamp = MicrosecondTimestamp::now();
        // Should be roughly current time
        let expected = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_micros() as u64;

        // Allow small difference (less than 1 second)
        assert!(timestamp.as_micros().abs_diff(expected) < 1_000_000);
    }

    #[test]
    fn test_system_time_conversion() {
        let system_time = SystemTime::now();
        let timestamp = MicrosecondTimestamp::from(system_time);
        let converted_back = SystemTime::from(timestamp);

        // Should be very close
        let duration = converted_back
            .duration_since(system_time)
            .unwrap_or_else(|_| system_time.duration_since(converted_back).unwrap());

        assert!(duration.as_micros() < 1000); // Less than 1ms difference
    }

    #[test]
    fn test_consensus_encoding() {
        let original = MicrosecondTimestamp::from_micros(1_653_195_600_123_456);

        // Encode
        let mut encoded = Vec::new();
        original.consensus_encode(&mut encoded).unwrap();

        // Decode
        let decoded = MicrosecondTimestamp::consensus_decode(&mut encoded.as_slice()).unwrap();

        assert_eq!(decoded, original);
    }

    #[test]
    fn test_default() {
        let timestamp = MicrosecondTimestamp::default();
        assert_eq!(timestamp.as_micros(), 0);
        assert_eq!(timestamp.as_secs(), 0);
    }

    #[test]
    fn test_display() {
        let timestamp = MicrosecondTimestamp::from_micros(1_653_195_600_123_456);
        assert_eq!(format!("{}", timestamp), "1653195600123456μs");
    }

    #[test]
    fn test_utility_functions() {
        assert_eq!(secs_to_micros(1653195600), 1_653_195_600_000_000);
        assert_eq!(micros_to_secs(1_653_195_600_123_456), 1653195600);
    }
}
