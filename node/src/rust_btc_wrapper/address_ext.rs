//! Referenced from https://github.com/rust-bitcoin/rust-bitcoin

use bitcoin::{
    address::script_pubkey::ScriptBufExt,
    base58, bech32,
    constants::{
        PUBKEY_ADDRESS_PREFIX_MAIN, PUBKEY_ADDRESS_PREFIX_TEST, SCRIPT_ADDRESS_PREFIX_MAIN,
        SCRIPT_ADDRESS_PREFIX_TEST,
    },
    key::PubkeyHash,
    script::{Builder, PushBytes, ScriptHash},
    Network, ScriptBuf, WitnessProgram, WitnessVersion,
};
use bitcoin_internals::array::ArrayExt;
use std::str::FromStr;

use crate::{
    error::{Base58Error, Bech32Error, InvalidLegacyPrefixError, ParseError, UnknownHrpError},
    rust_btc_wrapper::{
        hrp_ext::{Hrp as HRP, BC, BCRT, TB, TC},
        network_ext::NetworkExtension,
    },
};
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NetworkKind {
    /// The Bitcoin mainnet network.
    Main,
    /// Some kind of testnet network.
    Test,
}

// We explicitly do not provide `is_testnet`, using `!network.is_mainnet()` is less
// ambiguous due to confusion caused by signet/testnet/regtest.
impl NetworkKind {
    /// Returns true if this is real mainnet bitcoin.
    pub fn is_mainnet(&self) -> bool {
        *self == NetworkKind::Main
    }
}

impl From<NetworkExtension> for NetworkKind {
    fn from(n: NetworkExtension) -> Self {
        match n {
            NetworkExtension::Standard(network_type) => match network_type {
                bitcoin::Network::Bitcoin => Self::Main,
                _ => Self::Test,
            },
            NetworkExtension::Cpunet => Self::Test,
        }
    }
}
#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum KnownHrp {
    /// The main Bitcoin network.
    Mainnet,
    /// The test networks, testnet (testnet3), testnet4, and signet.
    Testnets,
    /// The regtest network.
    Regtest,
    /// The CPUNet test network.
    CPUNet,
}

impl KnownHrp {
    #[allow(unused)]
    fn from_network(network: NetworkExtension) -> Self {
        match network {
            NetworkExtension::Standard(network_type) => match network_type {
                Network::Bitcoin => Self::Mainnet,
                Network::Testnet(_) | Network::Signet => Self::Testnets,
                Network::Regtest => Self::Regtest,
                _ => Self::Mainnet,
            },
            NetworkExtension::Cpunet => Self::CPUNet,
        }
    }

    fn from_hrp(hrp: HRP) -> Result<Self, UnknownHrpError> {
        if hrp == BC {
            Ok(Self::Mainnet)
        } else if hrp == TB {
            Ok(Self::Testnets)
        } else if hrp == BCRT {
            Ok(Self::Regtest)
        } else if hrp == TC {
            Ok(Self::CPUNet)
        } else {
            Err(UnknownHrpError(hrp.to_lowercase()))
        }
    }
    #[allow(unused)]
    fn to_hrp(self) -> HRP {
        match self {
            Self::Mainnet => BC,
            Self::Testnets => TB,
            Self::Regtest => BCRT,
            Self::CPUNet => TC,
        }
    }
}

/// The inner representation of an address, without the network validation tag.
///
/// This struct represents the inner representation of an address without the network validation
/// tag, which is used to ensure that addresses are used only on the appropriate network.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AddressInner {
    P2pkh {
        hash: PubkeyHash,
        network: NetworkKind,
    },
    P2sh {
        hash: ScriptHash,
        network: NetworkKind,
    },
    Segwit {
        program: WitnessProgram,
        hrp: KnownHrp,
    },
}
pub struct Address(AddressInner);
impl Address {
    fn from_inner(inner: AddressInner) -> Self {
        Self(inner)
    }
    fn to_inner(self) -> AddressInner {
        self.0
    }
    /// Parses a bech32 Address string
    pub fn from_bech32_str(s: &str) -> Result<Self, Bech32Error> {
        let (hrp, witness_version, data) = bech32::segwit::decode(s)
            .expect("An error occurred while decoding the bech32 received in address");
        let version = WitnessVersion::try_from(witness_version.to_u8())?;
        let program = WitnessProgram::new(version, &data)
            .expect("bech32 guarantees valid program length for witness");
        let wrapped_hrp_ext = HRP {
            buf: hrp.as_bytes().try_into().unwrap(),
            size: hrp.len(),
        };
        let hrp = KnownHrp::from_hrp(wrapped_hrp_ext)
            .expect("An error occured while converting custom hrp to KnwonHrp type");
        let inner = AddressInner::Segwit { program, hrp };
        Ok(Self::from_inner(inner))
    }
    /// Parses a base58 Address string
    pub fn from_base58_str(s: &str) -> Result<Self, Base58Error> {
        if s.len() > 50 {
            // return Err(LegacyAddressTooLongError { length: s.len() }.into());
        }
        let data = base58::decode_check(s).unwrap();
        let data: &[u8; 21] = (&*data).try_into().unwrap();
        let (prefix, &data) = data.split_first();
        let inner = match *prefix {
            PUBKEY_ADDRESS_PREFIX_MAIN => {
                let hash = PubkeyHash::from_byte_array(data);
                AddressInner::P2pkh {
                    hash,
                    network: NetworkKind::Main,
                }
            }
            PUBKEY_ADDRESS_PREFIX_TEST => {
                let hash = PubkeyHash::from_byte_array(data);
                AddressInner::P2pkh {
                    hash,
                    network: NetworkKind::Test,
                }
            }
            SCRIPT_ADDRESS_PREFIX_MAIN => {
                let hash = ScriptHash::from_byte_array(data);
                AddressInner::P2sh {
                    hash,
                    network: NetworkKind::Main,
                }
            }
            SCRIPT_ADDRESS_PREFIX_TEST => {
                let hash = ScriptHash::from_byte_array(data);
                AddressInner::P2sh {
                    hash,
                    network: NetworkKind::Test,
                }
            }
            invalid => return Err(InvalidLegacyPrefixError { invalid }.into()),
        };

        Ok(Self::from_inner(inner))
    }
    /// Generates P2WSH-type of scriptPubkey with a given [`WitnessVersion`] and the program bytes.
    /// Does not do any checks on version or program length.
    ///
    /// Convenience method used by `new_p2a`, `new_p2wpkh`, `new_p2wsh`, `new_p2tr`, and `new_p2tr_tweaked`.
    fn new_witness_program_unchecked<T: AsRef<PushBytes>>(
        version: WitnessVersion,
        program: T,
    ) -> ScriptBuf {
        let program = program.as_ref();
        debug_assert!(program.len() >= 2 && program.len() <= 40);
        // In SegWit v0, the program must be either 20 bytes (P2WPKH) or 32 bytes (P2WSH) long.
        debug_assert!(version != WitnessVersion::V0 || program.len() == 20 || program.len() == 32);
        Builder::new()
            .push_opcode(version.into())
            .push_slice(program)
            .into_script()
    }
    /// Generates a script pubkey spending to this address.
    pub fn script_pubkey(&self) -> ScriptBuf {
        use AddressInner::*;
        match self.0 {
            P2pkh { hash, network: _ } => ScriptBuf::new_p2pkh(hash),
            P2sh { hash, network: _ } => ScriptBuf::new_p2sh(hash),
            Segwit {
                ref program,
                hrp: _,
            } => {
                let prog = program.program();
                let version = program.version();
                Self::new_witness_program_unchecked(version, prog)
            }
        }
    }
}
impl FromStr for Address {
    type Err = ParseError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        if ["bc1", "bcrt1", "tb1", "tc1"]
            .iter()
            .any(|&prefix| s.to_lowercase().starts_with(prefix))
        {
            let address = Address::from_bech32_str(s).unwrap();
            // We know that `U` is only ever `NetworkUnchecked` but the compiler does not.
            Ok(Self::from_inner(address.to_inner()))
        } else if ["1", "2", "3", "m", "n"]
            .iter()
            .any(|&prefix| s.starts_with(prefix))
        {
            let address = Address::from_base58_str(s).unwrap();
            Ok(Self::from_inner(address.to_inner()))
        } else {
            let hrp = match s.rfind('1') {
                Some(pos) => &s[..pos],
                None => s,
            };
            Err(UnknownHrpError(hrp.to_owned()).into())
        }
    }
}
