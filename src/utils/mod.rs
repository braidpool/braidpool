pub mod bitcoin;

// Standard Imports
use num_bigint::BigUint;
use hex;

// TODO: Implement the various traits for implicit conversions!
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Hash(pub [u8; 32]);

impl From<BigUint> for Hash {
    fn from(value: BigUint) -> Self {
        let mut bytes = value.to_bytes_le();
        bytes.resize(32, 0);

        let mut array = [0_u8; 32];
        array[0..].copy_from_slice(&bytes);

        Hash(array)
    }
}

impl Into<BigUint> for Hash {
    fn into(self) -> BigUint {
        BigUint::from_bytes_le(&self.0)
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
        let big_endian_bytes = hex::decode(hex).expect("Invalid hex string");
        let mut little_endian_bytes = big_endian_bytes.clone();
        little_endian_bytes.reverse();


        let mut array= [0u8; 32];
        array[0..].copy_from_slice(&little_endian_bytes);
        Hash(array)
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Byte(pub u8);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Bytes(pub Vec<Byte>);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Time(pub u32);