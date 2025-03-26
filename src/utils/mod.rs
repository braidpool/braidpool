pub mod bitcoin;

// Standard Imports
use num_bigint::BigUint;

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

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Byte(pub u8);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Bytes(pub Vec<Byte>);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Time(pub u32);