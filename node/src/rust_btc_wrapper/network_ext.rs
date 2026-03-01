//! Referenced from https://github.com/rust-bitcoin/rust-bitcoin

use bitcoin::{network::Network, TestnetVersion};
use core::fmt;
use serde::{de, Deserialize, Deserializer, Serialize, Serializer};
use std::str::FromStr;

use crate::rust_btc_wrapper::params_ext::{self, Params};

#[derive(Copy, PartialEq, Eq, PartialOrd, Ord, Clone, Hash, Debug)]
pub enum NetworkExtension {
    Standard(Network),
    Cpunet,
}

impl Serialize for NetworkExtension {
    fn serialize<S: Serializer>(&self, s: S) -> Result<S::Ok, S::Error> {
        let str_repr = match self {
            Self::Standard(Network::Bitcoin) => "bitcoin",
            Self::Standard(Network::Testnet(TestnetVersion::V3)) => "testnet",
            Self::Standard(Network::Testnet(TestnetVersion::V4)) => "testnet4",
            Self::Standard(Network::Signet) => "signet",
            Self::Standard(Network::Regtest) => "regtest",
            Self::Cpunet => "cpunet",
            // Default to bitcoin for unknown variants
            _ => "bitcoin",
        };
        s.serialize_str(str_repr)
    }
}

impl<'de> Deserialize<'de> for NetworkExtension {
    fn deserialize<D: Deserializer<'de>>(d: D) -> Result<Self, D::Error> {
        let s = String::deserialize(d)?;
        Self::from_str(&s).map_err(de::Error::custom)
    }
}

impl NetworkExtension {
    /// Returns the associated network parameters.
    pub fn params(self) -> &'static Params {
        match self {
            Self::Standard(Network::Bitcoin) => &params_ext::MAINNET,
            Self::Standard(Network::Testnet(TestnetVersion::V3)) => &params_ext::TESTNET3,
            Self::Standard(Network::Testnet(TestnetVersion::V4)) => &params_ext::TESTNET4,
            Self::Standard(Network::Testnet(_)) => &params_ext::TESTNET3,
            Self::Standard(Network::Signet) => &params_ext::SIGNET,
            Self::Standard(Network::Regtest) => &params_ext::REGTEST,
            Self::Standard(_) => &params_ext::MAINNET, // Default for unknown standard networks
            Self::Cpunet => &params_ext::CPUNET,
        }
    }

    pub fn to_core_arg(self) -> &'static str {
        match self {
            Self::Cpunet => "cpunet",
            Self::Standard(network_type) => {
                match network_type {
                    Network::Bitcoin => "main",
                    Network::Testnet(TestnetVersion::V3) => "test",
                    Network::Testnet(TestnetVersion::V4) => "testnet4",
                    Network::Signet => "signet",
                    Network::Regtest => "regtest",
                    //Default to mainnet if incompatible type is provided as input
                    _ => "main",
                }
            }
        }
    }
    pub fn from_core_arg(core_arg: &str) -> Result<Self, ParseNetworkError> {
        let network = match core_arg {
            "main" => Self::Standard(Network::Bitcoin),
            "test" => Self::Standard(Network::Testnet(TestnetVersion::V3)),
            "testnet4" => Self::Standard(Network::Testnet(TestnetVersion::V4)),
            "signet" => Self::Standard(Network::Signet),
            "regtest" => Self::Standard(Network::Regtest),
            "cpunet" => Self::Cpunet,
            _ => return Err(ParseNetworkError(InternalString(core_arg.to_owned()))),
        };
        Ok(network)
    }
    const fn as_display_str(self) -> &'static str {
        match self {
            Self::Cpunet => "cpunet",
            Self::Standard(network_type) => {
                match network_type {
                    Network::Bitcoin => "main",
                    // For user-side compatibility, testnet3 is retained as test
                    Network::Testnet(TestnetVersion::V3) => "test",
                    Network::Testnet(TestnetVersion::V4) => "testnet4",
                    Network::Signet => "signet",
                    Network::Regtest => "regtest",
                    //Default to mainnet if incompatible type is provided as input
                    _ => "main",
                }
            }
        }
    }
}
impl fmt::Display for NetworkExtension {
    fn fmt(&self, f: &mut core::fmt::Formatter) -> core::fmt::Result {
        write!(f, "{}", self.as_display_str())
    }
}
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct InternalString(pub String);
impl InternalString {
    pub fn display_cannot_parse<'a, T>(&'a self, what: &'a T) -> CannotParse<'a, T>
    where
        T: fmt::Display + ?Sized,
    {
        CannotParse {
            input: &self.0,
            what,
        }
    }
}
impl From<&str> for InternalString {
    fn from(value: &str) -> Self {
        InternalString(value.to_owned())
    }
}
pub struct CannotParse<'a, T: fmt::Display + ?Sized> {
    input: &'a String,
    what: &'a T,
}

impl<T: fmt::Display + ?Sized> fmt::Display for CannotParse<'_, T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "failed to parse '{}' as {}", self.input, self.what)
    }
}
/// An error in parsing network string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseNetworkError(InternalString);

impl fmt::Display for ParseNetworkError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        // Outputs 'failed to parse <input string> as network'.
        write!(f, "{}", self.0.display_cannot_parse("network"))
    }
}
impl std::error::Error for ParseNetworkError {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }
}
impl FromStr for NetworkExtension {
    type Err = ParseNetworkError;

    #[inline]
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "bitcoin" => Ok(Self::Standard(Network::Bitcoin)),
            // For user-side compatibility, testnet3 is retained as testnet
            "testnet" => Ok(Self::Standard(Network::Testnet(TestnetVersion::V3))),
            "testnet4" => Ok(Self::Standard(Network::Testnet(TestnetVersion::V4))),
            "signet" => Ok(Self::Standard(Network::Signet)),
            "regtest" => Ok(Self::Standard(Network::Regtest)),
            "cpunet" => Ok(Self::Cpunet),
            _ => Err(ParseNetworkError(InternalString::from(s))),
        }
    }
}

impl AsRef<Self> for NetworkExtension {
    fn as_ref(&self) -> &Self {
        self
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn network_ext_serde_roundtrip() {
        use std::{format, vec};

        use Network::*;

        let tests = vec![
            (NetworkExtension::Standard(Bitcoin), "bitcoin"),
            (
                NetworkExtension::Standard(Testnet(TestnetVersion::V3)),
                "testnet",
            ),
            (
                NetworkExtension::Standard(Testnet(TestnetVersion::V4)),
                "testnet4",
            ),
            (NetworkExtension::Standard(Signet), "signet"),
            (NetworkExtension::Standard(Regtest), "regtest"),
            (NetworkExtension::Cpunet, "cpunet"),
        ];

        for tc in tests {
            let network_ext = tc.0;

            let want = format!("\"{}\"", tc.1);
            let got = serde_json::to_string(&tc.0).expect("failed to serialize NetworkExtension");
            assert_eq!(got, want);

            let back: NetworkExtension =
                serde_json::from_str(&got).expect("failed to deserialize NetworkExtension");
            assert_eq!(back, network_ext);
        }
    }
}
