use bitcoin::consensus::encode::Decodable;
use bitcoin::consensus::encode::Encodable;
use bitcoin::io::{self, Read, Write};
use serde::Deserialize;
use serde::Serialize;
use std::time::SystemTime;
use std::time::UNIX_EPOCH;

pub const MICROS_PER_SEC: u64 = 1_000_000;

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

    pub fn from_secs(secs: u32) -> Self {
        Self(secs as u64 * MICROS_PER_SEC)
    }

    pub fn as_secs(self) -> u32 {
        (self.0 / MICROS_PER_SEC) as u32
    }

    pub fn now() -> Self {
        let micros = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map(|d| d.as_micros() as u64)
            .unwrap_or(0);
        Self(micros)
    }

    /// Convert to SystemTime
    pub fn to_system_time(self) -> SystemTime {
        UNIX_EPOCH + std::time::Duration::from_micros(self.0)
    }

    /// Convert from SystemTime
    pub fn from_system_time(time: SystemTime) -> Result<Self, std::time::SystemTimeError> {
        let micros = time.duration_since(UNIX_EPOCH)?.as_micros() as u64;
        Ok(Self(micros))
    }
}

impl Default for MicrosecondTimestamp {
    fn default() -> Self {
        Self(0)
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
    fn consensus_decode<R: Read + ?Sized>(
        r: &mut R,
    ) -> Result<Self, bitcoin::consensus::encode::Error> {
        let value = u64::consensus_decode(r)?;
        Ok(value.into())
    }
}

// Display formatting
impl std::fmt::Display for MicrosecondTimestamp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}us", self.0)
    }
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
        assert_eq!(i64::from(timestamp), original_micros as i64);
        assert_eq!(timestamp.as_secs(), 1653195600);
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
        assert!(timestamp.as_micros().abs_diff(expected) < MICROS_PER_SEC);
    }

    #[test]
    fn test_now_has_sub_second_precision() {
        let any_sub_second =
            (0..1000).any(|_| MicrosecondTimestamp::now().as_micros() % MICROS_PER_SEC != 0);
        assert!(any_sub_second, "now() is only producing whole seconds");
    }

    #[test]
    fn test_system_time_conversion() {
        let system_time = SystemTime::now();
        let timestamp = MicrosecondTimestamp::from_system_time(system_time).unwrap();
        let converted_back = SystemTime::from(timestamp);

        // Should be very close
        let duration = converted_back
            .duration_since(system_time)
            .unwrap_or_else(|_| system_time.duration_since(converted_back).unwrap());

        assert!(duration.as_micros() < 1000);
    }

    #[test]
    fn test_consensus_encoding() {
        let original = MicrosecondTimestamp::from_micros(1_653_195_600_123_456);

        // Encode
        let mut encoded = Vec::new();
        original.consensus_encode(&mut encoded).unwrap();

        assert_eq!(encoded.len(), 8);

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
    fn test_ordering_is_sub_second() {
        let a = MicrosecondTimestamp::from_micros(1_653_195_600_000_000);
        let b = MicrosecondTimestamp::from_micros(1_653_195_600_001_000);
        assert!(a < b);
        assert_eq!(a.as_secs(), b.as_secs());
    }
}
