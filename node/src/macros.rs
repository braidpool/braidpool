//! Macros for generating protocol enums with data-carrying variants

/// Generates protocol enums with automatic consensus encoding/decoding implementations.
/// Supports both unit variants and data-carrying variants.
///
/// This is intended for P2P messages which will be sent over the wire and assists in
/// creating an enum for a category of requests or responses.
///
/// Each generated enum has a `msg_id()` method that returns the discriminant value.
///
/// **Syntax:**
/// ```text
/// braidpool_protocol! {
///     pub enum MyProtocol {
///         FirstMessage            = 0,            // unit variant
///         SecondMessage(String)   = 1             // data-carrying with type
///     }
/// }
///
/// // Usage:
/// let msg = MyProtocol::FirstMessage;
/// assert_eq!(msg.msg_id(), 0);
/// ```
macro_rules! braidpool_protocol {
    // Entry point - generate full enum with all implementations
    (
        $(#[$meta:meta])*
        pub enum $name:ident {
            $($variants:tt)*
        }
    ) => {
        braidpool_protocol!(@generate
            [$(#[$meta])*]
            $name
            $($variants)*
        );
    };

    // Generate the enum and all implementations
    (@generate
        [$($meta:tt)*]
        $name:ident
        $($variants:tt)*
    ) => {
        $($meta)*
        #[derive(Clone, Debug, PartialEq)]
        #[repr(u8)]
        pub enum $name {
            $($variants)*
        }

        impl $name {
            pub fn msg_id(&self) -> u8 {
                braidpool_protocol!(@msg_id self, $name, $($variants)*)
            }
        }

        impl bitcoin::consensus::encode::Encodable for $name {
            fn consensus_encode<W: bitcoin::io::Write + ?Sized>(&self, w: &mut W) -> core::result::Result<usize, bitcoin::io::Error> {
                let mut len = 0;
                braidpool_protocol!(@encode self, w, len, $name, $($variants)*)
            }
        }

        impl bitcoin::consensus::encode::Decodable for $name {
            fn consensus_decode<R: bitcoin::io::BufRead + ?Sized>(r: &mut R) -> core::result::Result<Self, bitcoin::consensus::Error> {
                let discriminant = u8::consensus_decode(r)?;
                braidpool_protocol!(@decode discriminant, r, $name, $($variants)*)
            }
        }
    };

    // Message ID matching
    (@msg_id $self:ident, $name:ident,) => {
        panic!("Unreachable: All variants should be covered")
    };
    // Fallback for last element without trailing comma
    (@msg_id $self:ident, $name:ident, $variant:ident = $discrim:literal) => {
        $discrim
    };
    (@msg_id $self:ident, $name:ident, $variant:ident($type:ty) = $discrim:literal) => {
        $discrim
    };
    // Standard case with rest
    (@msg_id $self:ident, $name:ident, $variant:ident = $discrim:literal, $($rest:tt)*) => {
        if let $name::$variant = $self {
            $discrim
        } else {
            braidpool_protocol!(@msg_id $self, $name, $($rest)*)
        }
    };
    (@msg_id $self:ident, $name:ident, $variant:ident($type:ty) = $discrim:literal, $($rest:tt)*) => {
        if let $name::$variant(_) = $self {
            $discrim
        } else {
            braidpool_protocol!(@msg_id $self, $name, $($rest)*)
        }
    };

    // Encode implementation
    (@encode $self:ident, $w:ident, $len:ident, $name:ident, $($rest:tt)*) => {
        braidpool_protocol!(@encode_match $self, $w, $len, $name, $($rest)*)
    };

    (@encode_match $self:ident, $w:ident, $len:ident, $name:ident, $variant:ident = $discrim:literal, $($rest:tt)*) => {
        if let $name::$variant = $self {
            $len += ($discrim as u8).consensus_encode($w)?;
            Ok($len)
        } else {
            braidpool_protocol!(@encode_match $self, $w, $len, $name, $($rest)*)
        }
    };
    (@encode_match $self:ident, $w:ident, $len:ident, $name:ident, $variant:ident($type:ty) = $discrim:literal, $($rest:tt)*) => {
        if let $name::$variant(data) = $self {
            $len += ($discrim as u8).consensus_encode($w)?;
            $len += data.consensus_encode($w)?;
            Ok($len)
        } else {
            braidpool_protocol!(@encode_match $self, $w, $len, $name, $($rest)*)
        }
    };
    // Fallback for last element without trailing comma
    (@encode_match $self:ident, $w:ident, $len:ident, $name:ident, $variant:ident = $discrim:literal) => {
        $len += ($discrim as u8).consensus_encode($w)?;
        Ok($len)
    };
    (@encode_match $self:ident, $w:ident, $len:ident, $name:ident, $variant:ident($type:ty) = $discrim:literal) => {
        if let $name::$variant(data) = $self {
            $len += ($discrim as u8).consensus_encode($w)?;
            $len += data.consensus_encode($w)?;
            Ok($len)
        } else {
            panic!("Unreachable: All variants should be covered")
        }
    };
    (@encode_match $self:ident, $w:ident, $len:ident, $name:ident, $($rest:tt)*) => {
        panic!("Unreachable: All variants should be covered")
    };

    // Decode implementation
    (@decode $discrim:ident, $r:ident, $name:ident, $($rest:tt)*) => {
        braidpool_protocol!(@decode_match $discrim, $r, $name, $($rest)*)
    };

    (@decode_match $discrim:ident, $r:ident, $name:ident, $variant:ident = $expected:literal, $($rest:tt)*) => {
        if $discrim == $expected {
            Ok($name::$variant)
        } else {
            braidpool_protocol!(@decode_match $discrim, $r, $name, $($rest)*)
        }
    };
    (@decode_match $discrim:ident, $r:ident, $name:ident, $variant:ident($type:ty) = $expected:literal, $($rest:tt)*) => {
        if $discrim == $expected {
            Ok($name::$variant(<$type as bitcoin::consensus::encode::Decodable>::consensus_decode($r)?))
        } else {
            braidpool_protocol!(@decode_match $discrim, $r, $name, $($rest)*)
        }
    };
    // Fallback for last element without trailing comma
    (@decode_match $discrim:ident, $r:ident, $name:ident, $variant:ident = $expected:literal) => {
        if $discrim == $expected {
            Ok($name::$variant)
        } else {
            Err(bitcoin::consensus::Error::from(bitcoin::io::Error::new(
                bitcoin::io::ErrorKind::InvalidData,
                concat!("Invalid message id for ", stringify!($name)),
            )))
        }
    };
    (@decode_match $discrim:ident, $r:ident, $name:ident, $variant:ident($type:ty) = $expected:literal) => {
        if $discrim == $expected {
            Ok($name::$variant(<$type as bitcoin::consensus::encode::Decodable>::consensus_decode($r)?))
        } else {
            Err(bitcoin::consensus::Error::from(bitcoin::io::Error::new(
                bitcoin::io::ErrorKind::InvalidData,
                concat!("Invalid message id for ", stringify!($name)),
            )))
        }
    };
    (@decode_match $discrim:ident, $r:ident, $name:ident, $($rest:tt)*) => {
        Err(bitcoin::consensus::Error::from(bitcoin::io::Error::new(
            bitcoin::io::ErrorKind::InvalidData,
            concat!("Invalid message id for ", stringify!($name)),
        )))
    };
}

/// Implements Bitcoin consensus encoding for structs with named fields.
///
/// This macro generates `Encodable` and `Decodable` trait implementations that encode/decode
/// struct fields sequentially in the order specified. Includes OOM protection via `MAX_VEC_SIZE`.
///
/// **Syntax:** `impl_consensus_encoding!(StructName, field1, field2, field3);`
///
/// **Example:**
/// ```text
/// pub struct Transaction {
///     pub version: u32,
///     pub inputs: Vec<TxIn>,
///     pub outputs: Vec<TxOut>,
/// }
///
/// impl_consensus_encoding!(Transaction, version, inputs, outputs);
/// ```
///
/// Based on rust-bitcoin's implementation pattern:
/// <https://github.com/rust-bitcoin/rust-bitcoin/blob/master/p2p/src/consensus.rs>
macro_rules! impl_consensus_encoding {
    ($thing:ident, $($field:ident),+) => {
        impl bitcoin::consensus::encode::Encodable for $thing {
            #[inline]
            fn consensus_encode<W: bitcoin::io::Write + ?Sized>(
                &self,
                w: &mut W,
            ) -> core::result::Result<usize, bitcoin::io::Error> {
                let mut len = 0;
                $(len += self.$field.consensus_encode(w)?;)+
                Ok(len)
            }
        }

        impl bitcoin::consensus::encode::Decodable for $thing {
            #[inline]
            fn consensus_decode_from_finite_reader<R: bitcoin::io::BufRead + ?Sized>(
                r: &mut R,
            ) -> core::result::Result<$thing, bitcoin::consensus::encode::Error> {
                Ok($thing {
                    $($field: bitcoin::consensus::encode::Decodable::consensus_decode_from_finite_reader(r)?),+
                })
            }

            #[inline]
            fn consensus_decode<R: bitcoin::io::BufRead + ?Sized>(
                r: &mut R,
            ) -> core::result::Result<$thing, bitcoin::consensus::encode::Error> {
                use bitcoin::io::Read;
                let mut r = Read::take(r, bitcoin::consensus::encode::MAX_VEC_SIZE as u64);
                Ok($thing {
                    $($field: bitcoin::consensus::encode::Decodable::consensus_decode(&mut r)?),+
                })
            }
        }
    };
}

/// Implements traits for newtype wrappers around `Vec<T>`.
///
/// This macro generates implementations for wrapper types around `Vec<T>` to work around
/// Rust's orphan rule. It provides:
/// - `Deref` to `Vec<T>` for automatic method access
/// - `IntoIterator` for use in `for` loops
/// - `From<Vec<T>>` and `From<Wrapper>` for conversions
/// - `Encodable` and `Decodable` with OOM protection
///
/// **Syntax:** `impl_vec_wrapper!(WrapperName, ElementType);`
///
/// **Example:**
/// ```text
/// #[derive(Clone, Debug, PartialEq)]
/// pub struct Transactions(pub Vec<Transaction>);
///
/// impl_vec_wrapper!(Transactions, Transaction);
///
/// // Now you can use:
/// let txs: Transactions = vec![tx1, tx2].into();
/// for tx in txs { ... }
/// txs.len();  // Via Deref
/// ```
///
/// Based on rust-bitcoin's orphan rule workaround pattern:
/// <https://github.com/rust-bitcoin/rust-bitcoin/blob/master/p2p/src/consensus.rs>
macro_rules! impl_vec_wrapper {
    ($wrapper: ident, $type: ty) => {
        impl std::ops::Deref for $wrapper {
            type Target = Vec<$type>;

            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl IntoIterator for $wrapper {
            type Item = $type;
            type IntoIter = std::vec::IntoIter<$type>;

            fn into_iter(self) -> Self::IntoIter {
                self.0.into_iter()
            }
        }

        impl From<Vec<$type>> for $wrapper {
            fn from(v: Vec<$type>) -> Self {
                $wrapper(v)
            }
        }

        impl From<$wrapper> for Vec<$type> {
            fn from(w: $wrapper) -> Self {
                w.0
            }
        }

        impl bitcoin::consensus::encode::Encodable for $wrapper {
            #[inline]
            fn consensus_encode<W: bitcoin::io::Write + ?Sized>(
                &self,
                w: &mut W,
            ) -> core::result::Result<usize, bitcoin::io::Error> {
                use bitcoin::consensus::WriteExt;
                let mut len = 0;
                len += w.emit_compact_size(self.0.len())?;
                for c in self.0.iter() {
                    len += c.consensus_encode(w)?;
                }
                Ok(len)
            }
        }

        impl bitcoin::consensus::encode::Decodable for $wrapper {
            #[inline]
            fn consensus_decode_from_finite_reader<R: bitcoin::io::BufRead + ?Sized>(
                r: &mut R,
            ) -> core::result::Result<$wrapper, bitcoin::consensus::encode::Error> {
                use bitcoin::consensus::ReadExt;
                let len = r.read_compact_size()?;
                // Limit the initial vec allocation to at most 8,000 bytes, which is
                // sufficient for most use cases. We don't allocate more space upfront
                // than this, since `len` is an untrusted allocation capacity. If the
                // vector does overflow the initial capacity `push` will just reallocate.
                // Note: OOM protection relies on reader eventually running out of
                // data to feed us.
                let max_init_capacity = 8000 / core::mem::size_of::<$type>();
                let mut ret = Vec::with_capacity(core::cmp::min(len as usize, max_init_capacity));
                for _ in 0..len {
                    ret.push(<$type as bitcoin::consensus::encode::Decodable>::consensus_decode_from_finite_reader(r)?);
                }
                Ok($wrapper(ret))
            }

            fn consensus_decode<R: bitcoin::io::BufRead + ?Sized>(
                r: &mut R,
            ) -> core::result::Result<$wrapper, bitcoin::consensus::encode::Error> {
                Self::consensus_decode_from_finite_reader(r)
            }
        }
    };
}

#[cfg(test)]
mod tests {
    use crate::utils::BeadHash as TestBeadHash;
    use bitcoin::consensus::encode::{Decodable, Encodable};
    use std::str::FromStr;

    // Test 1: Unit variants only
    braidpool_protocol! {
        pub enum TestProtocol {
            Variant1 = 0,
            Variant2 = 1,
            Variant3 = 2,
        }
    }

    #[test]
    fn test_unit_variants() {
        let v1 = TestProtocol::Variant1;
        assert_eq!(v1.msg_id(), 0);

        let v2 = TestProtocol::Variant2;
        assert_eq!(v2.msg_id(), 1);

        let v3 = TestProtocol::Variant3;
        assert_eq!(v3.msg_id(), 2);
    }

    // Test 2: Data-carrying variants
    braidpool_protocol! {
        pub enum DataProtocol {
            Empty = 0,
            Value(u32) = 5,
            Text(String) = 10,
        }
    }

    #[test]
    fn test_data_carrying_variants() {
        let d1 = DataProtocol::Empty;
        assert_eq!(d1.msg_id(), 0);

        let d2 = DataProtocol::Value(42);
        assert_eq!(d2.msg_id(), 5);

        let d3 = DataProtocol::Text("hello".to_string());
        assert_eq!(d3.msg_id(), 10);
    }

    #[test]
    fn test_encode_decode_unit() {
        let original = TestProtocol::Variant2;
        let mut encoded = Vec::new();
        let len = original.consensus_encode(&mut encoded).unwrap();
        assert!(len > 0);

        let decoded = TestProtocol::consensus_decode(&mut encoded.as_slice()).unwrap();
        assert_eq!(decoded.msg_id(), original.msg_id());
        assert_eq!(decoded, TestProtocol::Variant2);
    }

    #[test]
    fn test_encode_decode_data() {
        let original = DataProtocol::Value(123);
        let mut encoded = Vec::new();
        let len = original.consensus_encode(&mut encoded).unwrap();
        assert!(len > 0);

        let decoded = DataProtocol::consensus_decode(&mut encoded.as_slice()).unwrap();
        assert_eq!(decoded.msg_id(), original.msg_id());

        if let DataProtocol::Value(val) = decoded {
            assert_eq!(val, 123);
        } else {
            panic!("Expected Value variant");
        }
    }

    // Test 3: BeadRequest pattern with Vec instead of HashSet for simplicity
    braidpool_protocol! {
        pub enum TestBeadRequest {
            GetBeads(Vec<TestBeadHash>) = 0,
            GetTips = 1,
            GetGenesis = 2,
        }
    }

    #[test]
    fn test_bead_request_pattern() {
        let mut hashes = Vec::new();
        hashes.push(
            TestBeadHash::from_str(
                "0000000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap(),
        );

        let req = TestBeadRequest::GetBeads(hashes.clone());
        assert_eq!(req.msg_id(), 0);

        let req2 = TestBeadRequest::GetTips;
        assert_eq!(req2.msg_id(), 1);

        let mut encoded = Vec::new();
        req.consensus_encode(&mut encoded).unwrap();

        let decoded = TestBeadRequest::consensus_decode(&mut encoded.as_slice()).unwrap();
        assert_eq!(decoded.msg_id(), req.msg_id());
    }

    #[test]
    fn test_all_variant_types() {
        // Test we can create different variants
        let _p1 = TestProtocol::Variant1;
        let _p2 = TestProtocol::Variant2;
        let _p3 = TestProtocol::Variant3;

        let _d1 = DataProtocol::Empty;
        let _d2 = DataProtocol::Value(42);
        let _d3 = DataProtocol::Text("hello".to_string());

        let mut hashes = Vec::new();
        hashes.push(
            TestBeadHash::from_str(
                "0000000000000000000000000000000000000000000000000000000000000000",
            )
            .unwrap(),
        );
        let _br1 = TestBeadRequest::GetBeads(hashes);
        let _br2 = TestBeadRequest::GetTips;
        let _br3 = TestBeadRequest::GetGenesis;

        // Just verify compilation - all enums can be created
        assert!(true);
    }
}
