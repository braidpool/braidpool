//! Referenced from https://github.com/rust-bitcoin/rust-bech32

use core::slice;

const MAX_HRP_LEN: usize = 83;
/// The human-readable part (human readable prefix before the '1' separator).
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Hrp {
    pub buf: [u8; MAX_HRP_LEN],
    pub size: usize,
}
/// Iterator over bytes (ASCII values) of the human-readable part.
///
/// ASCII byte values as they were initially parsed (i.e., in the original case).
pub struct ByteIter<'b> {
    iter: slice::Iter<'b, u8>,
}
fn is_ascii_uppercase(b: u8) -> bool {
    (65..=90).contains(&b)
}

impl Iterator for ByteIter<'_> {
    type Item = u8;
    #[inline]
    fn next(&mut self) -> Option<u8> {
        self.iter.next().copied()
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// Iterator over lowercase bytes (ASCII characters) of the human-readable part.
pub struct LowercaseByteIter<'b> {
    iter: ByteIter<'b>,
}

impl Iterator for LowercaseByteIter<'_> {
    type Item = u8;
    #[inline]
    fn next(&mut self) -> Option<u8> {
        self.iter
            .next()
            .map(|b| if is_ascii_uppercase(b) { b | 32 } else { b })
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

/// Iterator over lowercase ASCII characters of the human-readable part.
pub struct LowercaseCharIter<'b> {
    iter: LowercaseByteIter<'b>,
}

impl Iterator for LowercaseCharIter<'_> {
    type Item = char;
    #[inline]
    fn next(&mut self) -> Option<char> {
        self.iter.next().map(Into::into)
    }
    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}
impl Hrp {
    #[inline]
    pub fn byte_iter(&self) -> ByteIter<'_> {
        ByteIter {
            iter: self.buf[..self.size].iter(),
        }
    }
    /// Creates a lowercase iterator over the byte values (ASCII characters) of this HRP.
    #[inline]
    pub fn lowercase_byte_iter(&self) -> LowercaseByteIter<'_> {
        LowercaseByteIter {
            iter: self.byte_iter(),
        }
    }
    /// Creates a lowercase character iterator over the ASCII characters of this HRP.
    #[inline]
    pub fn lowercase_char_iter(&self) -> LowercaseCharIter<'_> {
        LowercaseCharIter {
            iter: self.lowercase_byte_iter(),
        }
    }
    #[inline]
    pub fn to_lowercase(&self) -> String {
        self.lowercase_char_iter().collect()
    }
}
/// proc-macros defining the formation of Hrp struct provided with data-bytes and hrp_size 
#[rustfmt::skip]
macro_rules! define_hrp_const {
    (
        #[$doc:meta]
        pub const $name:ident $size:literal $v:expr;
    ) => {
        #[$doc]
        pub const $name: Hrp = Hrp { buf: [
            $v[0], $v[1], $v[2], $v[3],
            0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
        ], size: $size };
    };
}
define_hrp_const! {
    /// The human-readable part used by the Bitcoin mainnet network.
    pub const BC 2 [98, 99, 0, 0];
}
define_hrp_const! {
    /// The human-readable part used by the Bitcoin testnet networks (testnet, signet).
    pub const TB 2 [116, 98, 0, 0];
}
define_hrp_const! {
    /// The human-readable part used when running a Bitcoin regtest network.
    pub const BCRT 4 [98, 99, 114, 116];
}
define_hrp_const! {
    /// The human-readable part used by the Bitcoin cpunet network.
    pub const TC 2 [116, 99, 0, 0];
}
