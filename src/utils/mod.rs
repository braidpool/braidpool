pub mod bitcoin;

// TODO: Implement the various traits for implicit conversions!
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct Hash(pub [u64; 4]);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Byte(pub u8);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Bytes(pub Vec<Byte>);

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Time(pub u32);