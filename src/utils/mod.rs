pub mod bitcoin;

// Standard Imports
use num_bigint::BigUint;
use hex;

// TODO: Implement the various traits for implicit conversions!
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Hash(pub [u8; 32]);

impl From<BigUint> for Hash {
    fn from(value: BigUint) -> Self {
        let mut bytes = value.to_bytes_be();
        bytes.resize(32, 0);

        let mut array = [0u8; 32];
        for i in 0..32 {
            array[i] = bytes[i];
        };

        Hash(array)
    }
}

impl Into<BigUint> for Hash {
    fn into(self) -> BigUint {
        BigUint::from_bytes_be(&self.0)
    }
}

impl From<String> for Hash {
    fn from(hex: String) -> Self {
        Hash::from(hex.as_str())
    }
}

impl From<&str> for Hash {
    fn from(hex: &str) -> Self {
        let hex = hex.trim_start_matches("0x");
        let mut bytes = hex::decode(hex).expect("Invalid hex string");
        bytes.resize(32, 0);

        let mut array = [0u8; 32];
        for i in 0..32 {
            array[i] = bytes[i];
        };

        Hash(array)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Byte(pub u8);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Bytes(pub Vec<Byte>);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Time(pub u32);