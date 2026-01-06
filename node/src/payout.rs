use bitcoin::absolute::MedianTimePast;
use bitcoin::{Amount, CompactTarget, Network, Params, Target, Work};
use core::ops::Add;
use std::collections::BinaryHeap;
use std::collections::HashMap;
use std::error::Error;
//Containing functionality related to difficulty adjustment for braidpool currently static
//TODO: currently it will only be placeholder for modifying min_target accordingly for weaker_difficulty

pub struct DifficultyAdjuster {
    /// Current client difficulty setting
    pub current_difficulty: Target,
    /// Previous difficulty before a change
    pub old_difficulty: Target,
}
pub trait DifficultyAdjustmentTrait {
    fn get_current_difficulty(&self) -> Target;
    fn get_new_difficulty(&mut self, initial_target: Option<CompactTarget>) -> Target;
    fn new() -> Self;
}
impl DifficultyAdjustmentTrait for DifficultyAdjuster {
    fn new() -> Self {
        let zero_work = Target::ZERO;
        Self {
            current_difficulty: zero_work,
            //At initialization this shall be work computed according to `start_target` but for time being it is taken as Work(0)
            old_difficulty: zero_work,
        }
    }
    fn get_current_difficulty(&self) -> Target {
        self.current_difficulty
    }
    fn get_new_difficulty(&mut self, initial_target: Option<CompactTarget>) -> Target {
        if let Some(start_target) = initial_target {
            self.current_difficulty = Target::from_compact(start_target);
            self.old_difficulty = Target::from_compact(start_target);
        };
        self.current_difficulty
    }
}
impl DifficultyAdjuster {
    pub fn new() -> Self {
        let zero_work = Target::ZERO;
        Self {
            current_difficulty: zero_work,
            old_difficulty: zero_work,
        }
    }
}
#[derive(Debug)]
pub enum PayoutCommands {
    UpdatePayoutHeap {
        bead_timestamp: MedianTimePast,
        payout_address: String,
        work: Work,
    },
    GeneratePayout {
        payout_sender: std::sync::mpsc::Sender<Vec<OutputPair>>,
        total_difficulty: f64,
        total_amount: Amount,
    },
}
pub struct Payout {
    //Intializing mapping heap that will listen for new beads and update accordingly
    //Sorted mapping of only required information instead of complete `Bead` which will be updated on the arrival of beads
    payout_heap: BinaryHeap<(MedianTimePast, (Work, String))>,
    //Payout command receiver
    payout_cmd_receiver: std::sync::mpsc::Receiver<PayoutCommands>,
    //Configured network wrt which payout is being generated
    configured_network: Network,
}
#[derive(Debug, Clone)]
pub struct OutputPair {
    pub address: bitcoin::Address,
    pub amount: bitcoin::Amount,
}

impl Payout {
    pub fn new(configured_network: Network) -> (Self, std::sync::mpsc::Sender<PayoutCommands>) {
        let (payout_cmd_tx, payout_cmd_rx) = std::sync::mpsc::channel::<PayoutCommands>();
        (
            Payout {
                payout_heap: BinaryHeap::new(),
                payout_cmd_receiver: payout_cmd_rx,
                configured_network,
            },
            payout_cmd_tx,
        )
    }
    //Address::Work for beads belonging to same address
    fn _compute_work_mapping(&self) -> Result<HashMap<String, Work>, Box<dyn Error + Send + Sync>> {
        let mut work_mapping: HashMap<String, Work> = HashMap::new();
        for (_bead_timestamp, (bead_work, miner_payout_address)) in self.payout_heap.iter() {
            if work_mapping.contains_key(miner_payout_address) {
                if let Some(existing_work) = work_mapping.get_mut(miner_payout_address) {
                    *existing_work = Add::add(*existing_work, *bead_work);
                }
            } else {
                work_mapping.insert(miner_payout_address.clone(), *bead_work);
            }
        }
        Ok(work_mapping)
    }
    fn get_difficulty_window_shares(
        &self,
        total_difficulty: f64,
    ) -> Result<Vec<(String, f64)>, Box<dyn Error + Send + Sync>> {
        let mut result_values: Vec<(String, f64)> = Vec::new();
        let mut running_difficulty: f64 = 0.0;
        let network_params = match self.configured_network {
            Network::Bitcoin => Params::BITCOIN,
            Network::CPUNet => Params::CPUNET,
            Network::Regtest => Params::REGTEST,
            Network::Signet => Params::SIGNET,
            Network::Testnet(bitcoin::TestnetVersion::V4) => Params::TESTNET4,
            Network::Testnet(bitcoin::TestnetVersion::V3) => Params::TESTNET3,
            _ => Params::MAINNET,
        };
        // Query shares in batches going back in time
        for (_bead_timestamp, (bead_work, miner_payout_address)) in self.payout_heap.iter() {
            let curr_bead_difficulty = bead_work
                .to_target()
                .difficulty_float(network_params.clone());
            if running_difficulty < total_difficulty {
                running_difficulty += curr_bead_difficulty;
                result_values.push((miner_payout_address.clone(), curr_bead_difficulty));
            } else {
                break;
            }
        }
        Ok(result_values)
    }
    pub fn payout_runner(&mut self) {
        while let Ok(payout_cmd) = self.payout_cmd_receiver.recv() {
            tracing::info!("Payout runner initialize and received command succesfully");
            match payout_cmd {
                PayoutCommands::GeneratePayout {
                    payout_sender,
                    total_difficulty,
                    total_amount,
                } => {
                    let payout_distribution = match self
                        .get_output_distribuition(total_difficulty, total_amount)
                    {
                        Ok(reward_distribution) => reward_distribution,
                        Err(error) => {
                            tracing::error!(
                                    "An error occurred while generating payout distribution - {}, skipping generation.",
                                    error
                                );
                            continue;
                        }
                    };
                    match payout_sender.send(payout_distribution) {
                        Ok(_) => {
                            tracing::info!(
                                "Payout distribution sent to template_creator successfully !"
                            );
                        }
                        Err(_) => {
                            tracing::error!(
                                "An error occurred while sending payout distrubtion to downstream"
                            );
                        }
                    }
                }
                PayoutCommands::UpdatePayoutHeap {
                    bead_timestamp,
                    payout_address,
                    work,
                } => {
                    self.payout_heap
                        .push((bead_timestamp, (work, payout_address)));
                }
            }
        }
    }
    fn group_shares_by_address(address_work_pairs: &[(String, f64)]) -> HashMap<String, f64> {
        let mut address_difficulty_map = HashMap::new();
        for (address, bead_work) in address_work_pairs {
            *address_difficulty_map.entry(address.clone()).or_insert(0.0) += bead_work;
        }
        address_difficulty_map
    }
    fn append_proportional_distribution(
        address_difficulty_map: HashMap<String, f64>,
        total_amount: bitcoin::Amount,
        distribution: &mut Vec<OutputPair>,
    ) -> Result<(), Box<dyn Error + Send + Sync>> {
        let total_difficulty: f64 = address_difficulty_map.values().sum();
        let mut distributed_amount = bitcoin::Amount::ZERO;

        for (i, (address_str, difficulty)) in address_difficulty_map.iter().enumerate() {
            let address = address_str
                .parse::<bitcoin::Address<_>>()
                .map_err(|e| format!("Invalid bitcoin address '{address_str}': {e}"))?
                .assume_checked();

            let amount: Amount = if i == address_difficulty_map.len() - 1 {
                // Last address gets remainder to handle rounding
                let left_amount = core::ops::Sub::sub(total_amount, distributed_amount).unwrap();
                left_amount
            } else {
                let proportion = *difficulty / total_difficulty;
                let amount_sats = (total_amount.to_sat() as f64 * proportion).round() as u64;
                bitcoin::Amount::from_sat(amount_sats).unwrap()
            };

            distributed_amount = core::ops::Add::add(distributed_amount, amount).unwrap();
            distribution.push(OutputPair { address, amount });
        }
        Ok(())
    }
    fn get_output_distribuition(
        &self,
        total_difficulty: f64,
        total_amount: bitcoin::Amount,
    ) -> Result<Vec<OutputPair>, Box<dyn Error + Send + Sync>> {
        let beads = self.get_difficulty_window_shares(total_difficulty)?;
        if beads.is_empty() {
            return Ok(vec![]);
        }
        let mut distribution = Vec::<OutputPair>::with_capacity(beads.len());

        let address_difficulty_map = Self::group_shares_by_address(&beads);
        Self::append_proportional_distribution(
            address_difficulty_map,
            total_amount,
            &mut distribution,
        )?;
        Ok(distribution)
    }
}
