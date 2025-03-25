pub mod bitcoin;

// TODO: Implement the various traits for implicit conversions!
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Hash([u64; 4]);

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Byte(u8);

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Bytes(Vec<Byte>);

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Time(u32);