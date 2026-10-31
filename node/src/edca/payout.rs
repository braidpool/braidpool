use super::settle::{settle_totals, PayoutEntity, PayoutEntry};
use super::state::{EdcaState, MinerKey};
use crate::config::PoolNetwork;
use crate::error::EdcaError;
use bitcoin::address::AddressType;
use bitcoin::{Address, Amount, ScriptBuf, TxOut};
use braidpool_common::cpunet::Cpunet;
use std::cmp::Reverse;
use std::collections::BTreeMap;
use std::str::FromStr;
use tracing::debug;

/// Maximum number of miner payout outputs placed in a single coinbase.
pub const MAX_PAYOUT_OUTPUTS: usize = 64;

/// Maximum length of the pool identifier in the coinbase scriptSig, in bytes.
pub const MAX_POOL_IDENTIFIER_LEN: usize = 20;

/// A settled payout roster, ready to be spliced into a coinbase transaction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PayoutDistribution {
    pub outputs: Vec<TxOut>,
    pub settlement: PayoutEntity,
    pub over_budget: Vec<MinerKey>,
}

impl PayoutDistribution {
    /// Returns the total value carried by the payout outputs.
    pub fn total_value(&self) -> Amount {
        let satoshis = self.outputs.iter().fold(0u64, |sum, output| {
            sum.saturating_add(output.value.to_sat())
        });
        Amount::from_sat(satoshis.min(Amount::MAX_MONEY.to_sat()))
    }
}

/// Resolves a payout address string to a `scriptPubKey` for `network`.
pub fn resolve_payout_script(payout_address: &str, network: PoolNetwork) -> Option<ScriptBuf> {
    match network {
        PoolNetwork::Cpunet => {
            let script = Cpunet::decode_bech32_address(payout_address).ok()?;
            (script.is_p2wpkh() || script.is_p2wsh() || script.is_p2tr()).then_some(script)
        }
        PoolNetwork::Bitcoin(bitcoin_network) => {
            let address = Address::from_str(payout_address)
                .ok()?
                .require_network(bitcoin_network)
                .ok()?;
            match address.address_type()? {
                AddressType::P2pkh
                | AddressType::P2sh
                | AddressType::P2wpkh
                | AddressType::P2wsh
                | AddressType::P2tr => Some(address.script_pubkey()),
                _ => None,
            }
        }
    }
}

/// Builds the coinbase payout roster for a block reward.
pub fn build_payout_distribution(
    state: &EdcaState,
    total_reward: Amount,
    network: PoolNetwork,
    max_outputs: usize,
) -> Result<PayoutDistribution, EdcaError> {
    let mut by_script: BTreeMap<ScriptBuf, (MinerKey, u128)> = BTreeMap::new();

    for (address, weight) in state.miner_totals()? {
        let Some(script) = resolve_payout_script(&address, network) else {
            return Err(EdcaError::UnresolvedPayoutAddress {
                payout_address: address,
            });
        };
        let entry = by_script.entry(script).or_insert((address.clone(), 0));
        // The lowest address wins the tie-break, so the merged key is
        // the same on every node.
        if address < entry.0 {
            entry.0 = address.clone();
        }
        entry.1 = entry
            .1
            .checked_add(weight)
            .ok_or(EdcaError::WeightOverflow)?;
    }

    let mut resolved: Vec<(MinerKey, u128, ScriptBuf)> = by_script
        .into_iter()
        .map(|(script, (address, weight))| (address, weight, script))
        .collect();

    // Heaviest first, address as a deterministic tie-break, so the output
    // budget always keeps the same miners on every node.
    resolved.sort_by(|left, right| (Reverse(left.1), &left.0).cmp(&(Reverse(right.1), &right.0)));

    let mut over_budget: Vec<MinerKey> = Vec::new();
    if resolved.len() > max_outputs {
        for (address, _, _) in resolved.drain(max_outputs..) {
            debug!(
                payout_address = %address,
                max_outputs,
                "Deferring miner payout - coinbase output budget is full"
            );
            over_budget.push(address);
        }
        over_budget.sort();
    }

    let scripts: BTreeMap<MinerKey, ScriptBuf> = resolved
        .iter()
        .map(|(address, _, script)| (address.clone(), script.clone()))
        .collect();
    let weights: BTreeMap<MinerKey, u128> = resolved
        .into_iter()
        .map(|(address, weight, _)| (address, weight))
        .collect();

    let settlement = settle_totals(
        &weights,
        total_reward.to_sat(),
        state.config().dust_limit_sats,
    )?;

    // Largest payout first; the settlement itself is ordered by address.
    let mut paid: Vec<&PayoutEntry> = settlement.entries.iter().collect();
    paid.sort_by(|left, right| {
        (Reverse(left.value_sats), &left.address).cmp(&(Reverse(right.value_sats), &right.address))
    });

    let mut outputs = Vec::with_capacity(paid.len());
    for entry in paid {
        let Some(script) = scripts.get(&entry.address) else {
            // Unreachable: every settled address was resolved above.
            return Err(EdcaError::UnresolvedPayoutAddress {
                payout_address: entry.address.clone(),
            });
        };
        outputs.push(TxOut {
            value: Amount::from_sat(entry.value_sats),
            script_pubkey: script.clone(),
        });
    }

    Ok(PayoutDistribution {
        outputs,
        settlement,
        over_budget,
    })
}
