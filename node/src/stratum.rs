use crate::error::StratumErrors;
use crate::template_creator::calculate_merkle_root;
use crate::{EXTRANONCE1_SIZE, EXTRANONCE2_SIZE, EXTRANONCE_SEPARATOR};
use bitcoin::block::HeaderExt;
use bitcoin::consensus::serialize;
use bitcoin::io::Cursor;
use bitcoin::{absolute::Decodable, Transaction};
use bitcoin::{BlockHash, BlockHeader, BlockTime, TxMerkleNode, Txid, Witness};
use core::panic;
use futures::{lock::Mutex, FutureExt};
use rand::RngCore;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::{collections::HashMap, net::SocketAddr, sync::Arc};
use tokio::{
    io::{AsyncWriteExt, BufReader},
    net::{
        tcp::{OwnedReadHalf, OwnedWriteHalf},
        TcpListener,
    },
    sync::mpsc,
};
use tokio_stream::StreamExt;
use tokio_util::codec::{FramedRead, LinesCodec};
/*
1)Creating a `notifier` struct that will contain a notification sender along with another attribute of `notification` which will contain all the fields related to mining.notify endpoint from server2client method in stratumcontaining functions such as building
notification for a given block template received
2)Running a notifier in a separate task listening for new `templates` and after recieving those a new notification is constructed i.e. a valid job format and sent
to the downstream node .
3)A bifurcation of commands such as send to all clients and send to a particular downstream node that will be enabled via a command sender and command reciever, command sender will be passed
for each new connection and event mapped into the handle_connection function will serve for writing to the tcp_stream .
4)All the jobs currently will have to be mapped with all its data sent to a downstream and also the modified values received from the downstream node pertaining for the reconstruction of a valid
weak_share or `Bead` in case of braidpool is concerned hence a mapping required for storing all the jobs along with their job_id as well as the template used for generating that job by a valid downstream
node . Which further can be accessed by all the downstream nodes for methods such as mining.getjob(job_id) .
*/

/// Represents the `getblocktemplate` RPC response from Bitcoin Core.
///
/// Based on [BIP-0022](https://github.com/bitcoin/bips/blob/master/bip-0022.mediawiki) and
/// [Bitcoin Core implementation](https://github.com/bitcoin/bitcoin/blob/master/src/rpc/mining.cpp).
///
/// Contains all fields necessary for constructing a valid mining job, including
/// block version, previous block hash, transactions, coinbase data, target, and
/// various consensus limits.
#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct BlockTemplate {
    pub version: bitcoin::block::Version,
    pub rules: Option<Vec<String>>,
    pub vbavailable: Option<Vec<(String, i32)>>,
    pub vbrequired: Option<u32>,
    pub previousblockhash: BlockHash,
    pub transactions: Vec<Transaction>,
    pub coinbaseaux: Option<Vec<(String, String)>>,
    pub coinbasevalue: Option<u64>,
    pub longpollid: Option<String>,
    pub target: bitcoin::Target,
    pub mintime: Option<bitcoin::time::BlockTime>,
    pub mutable: Option<Vec<String>>,
    pub noncerange: Option<String>,
    pub sigoplimit: Option<u32>,
    pub sizelimit: Option<usize>,
    pub weightlimit: Option<bitcoin::blockdata::Weight>,
    pub curtime: bitcoin::time::BlockTime,
    pub bits: bitcoin::CompactTarget,
    pub height: bitcoin::absolute::Height,
    pub default_witness_commitment: Option<Witness>,
}
impl Default for BlockTemplate {
    fn default() -> Self {
        Self {
            version: bitcoin::block::Version::TWO,
            rules: None,
            vbavailable: None,
            vbrequired: None,
            previousblockhash: BlockHash::GENESIS_PREVIOUS_BLOCK_HASH,
            transactions: Vec::new(),
            coinbaseaux: None,
            coinbasevalue: None,
            longpollid: None,
            target: bitcoin::Target::MAX,
            mintime: None,
            mutable: None,
            noncerange: None,
            sigoplimit: None,
            sizelimit: None,
            weightlimit: None,
            curtime: bitcoin::BlockTime::from_u32(1759998900),
            bits: bitcoin::CompactTarget::from_consensus(0),
            height: bitcoin::absolute::Height::ZERO,
            default_witness_commitment: None,
        }
    }
}
#[derive(Debug, Clone)]
/// Configuration parameters for the Stratum server.
///
/// Defines network binding details, difficulty settings,
/// and optional solo mining payout address.
pub struct StratumServerConfig {
    /// Hostname or IP address to bind the Stratum server.
    pub hostname: String,
    /// TCP port for incoming Stratum connections.
    pub port: u16,
    /// Initial mining difficulty assigned to new clients as per in the `braidpool_spec.md`.
    pub start_difficulty: u64,
    /// Minimum allowed mining difficulty as per in the `braidpool_spec.md`.
    pub minimum_difficulty: u64,
    /// Optional maximum allowed mining difficulty.
    pub maximum_difficulty: Option<u64>,
    /// Optional payout address for solo mining mode.
    pub solo_address: Option<String>,
}

impl Default for StratumServerConfig {
    fn default() -> Self {
        Self {
            hostname: String::from("0.0.0.0"),
            port: 3333,
            //Placeholders can be changed in default
            start_difficulty: 1,
            minimum_difficulty: 1,
            maximum_difficulty: None,
            solo_address: None,
        }
    }
}
/// Represents a standard `Client → Server` Stratum request.
///
/// Covers common methods such as:
/// - `mining.authorize`
/// - `mining.configure`
/// - `mining.set_difficulty`
#[derive(Clone, Serialize, Deserialize, Debug, PartialEq, Eq)]
pub struct StandardRequest {
    pub id: u64,
    pub method: String,
    pub params: serde_json::Value,
}
/// Possible responses from the Stratum server.
///
/// Encapsulates both standard JSON-RPC responses and
/// protocol-specific responses such as difficulty suggestions.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum StratumResponses {
    //For standard requests
    StandardResponse {
        std_response: StandardResponse,
    },
    //For difficulty request since it is `notified request` not necessarily and stratum supported method
    SuggestDifficultyResponse {
        suggest_difficulty_resp: SuggestDifficultyResponse,
    },
}
/// Response represents a Stratum response message from the server to the client
/// We use Value in result to allow for different types of responses.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct StandardResponse {
    pub id: Option<u64>,
    pub result: Option<Value>,
    pub error: Option<String>,
}
impl StandardResponse {
    pub fn new_ok(id: Option<u64>, result: Value) -> Self {
        StandardResponse {
            id,
            result: Some(result),
            error: None,
        }
    }
}
///`Notfication` method responses specific to `mining.notify` and `mining.set_difficulty` responses
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JobNotificationResponse {
    pub method: String,
    pub params: serde_json::Value,
}
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SuggestDifficultyResponse {
    pub method: String,
    pub params: Vec<u64>,
}
///This will persist the client specific information for each of the new downstream connected
/// to the stratum service which are setup during either `mining.subscribe` or `mining.configure` or `mining.authorize`
#[derive(Debug, Clone)]
pub struct DownstreamClient {
    ///Authorized or not
    pub authorized: bool,
    ///Downstream miner IP
    pub downstream_ip: String,
    /// Did the mine subscribe already
    pub subscribed: bool,
    ///Diffculty suggested or not
    pub suggest_difficulty_done: bool,
    ///Configuration done so that all the phases are tracked and thus template can be supplied to downstream
    pub channel_configured: bool,
    /// The unique identifier assigned to this downstream connection/channel.
    #[allow(unused)]
    pub(super) connection_id: u32,
    /// The extranonce1 value assigned to this downstream miner.
    extranonce1: Vec<u8>,
    /// `extranonce1` to be sent to the Downstream in the SV1 `mining.subscribe` message response.
    //extranonce1: Vec<u8>,
    //extranonce2_size: usize,
    /// Version rolling mask bits `HexU32Be` used in case of considering SV2 for cross checking purposes
    version_rolling_mask: Option<String>,
    /// Minimum version rolling mask bits size
    version_rolling_min_bit: Option<u32>,
    /// The expected size of the extranonce2 field provided by the miner.
    extranonce2_len: usize,
    /// Optional per-connection monitoring target (stricter than share/weak target).
    /// Used to sample miner health at a higher rate than the share target.
    pub monitor_target: Option<bitcoin::Target>,
}
impl DownstreamClient {
    /// Handles an incoming Stratum `Client2Server` request from a downstream miner.
    ///
    /// Routes the request to the appropriate handler based on its `method`:
    /// - `mining.configure`
    /// - `mining.subscribe`
    /// - `mining.authorize`
    /// - `mining.submit`
    /// - `mining.set_difficulty`
    ///
    /// Sends the corresponding response back to the client and, if the client
    /// has been both authorized and subscribed, triggers sending the latest
    /// block template via the `notification_sender`.
    ///
    /// # Returns
    /// A `StratumResponses` variant on success, or a `StratumErrors` on failure.
    pub async fn handle_client_to_server_request(
        &mut self,
        client_request: StandardRequest,
        mining_job_map: Arc<Mutex<MiningJobMap>>,
        response_message_sender: mpsc::Sender<String>,
        notification_sender: mpsc::Sender<NotifyCmd>,
        peer_addr: String,
    ) -> Result<StratumResponses, StratumErrors> {
        let req_params = client_request.params;
        let method = client_request.method.clone();
        let client_request_id = client_request.id;
        let response_or_error = match method.as_ref() {
            "mining.configure" => self.handle_configure(&req_params, client_request_id).await,
            "mining.subscribe" => {
                Self::handle_subscribe(self, &req_params, client_request_id).await
            }
            "mining.authorize" => self.handle_authorize(&req_params, client_request_id).await,
            "mining.submit" => {
                Self::handle_submit(self, &req_params, mining_job_map, client_request_id).await
            }
            "mining.suggest_difficulty" => self.suggest_difficulty(&req_params).await,
            method => Err(StratumErrors::InvalidMethod {
                method: method.to_string(),
            }),
        };
        match response_or_error {
            Ok(stratum_response) => {
                let response_json_string = match stratum_response.clone() {
                    StratumResponses::StandardResponse { std_response } => {
                        serde_json::to_string(&std_response).unwrap()
                    }
                    StratumResponses::SuggestDifficultyResponse {
                        suggest_difficulty_resp,
                    } => serde_json::to_string(&suggest_difficulty_resp).unwrap(),
                };
                log::info!("Response received is - {:?}", response_json_string);
                log::info!(
                    "Sending response of the request {:?} to the downstream",
                    client_request.method
                );
                match response_message_sender.send(response_json_string).await {
                    Ok(_) => {
                        log::info!("Message sent successfully to the writer task");
                    }
                    Err(error) => {
                        log::error!(
                            "An error occurred while sending response to the writer task - {}",
                            error
                        );
                    }
                };
                //Sending the initial latest avaialble template to the recently subscribed and authorized
                //downstream connection
                if self.authorized == true
                    && self.subscribed == true
                    && self.channel_configured == true
                    && self.suggest_difficulty_done == true
                    && method != "mining.submit"
                {
                    let notification_sent_res = notification_sender
                        .send(NotifyCmd::SendLatestTemplateToNewDownstream {
                            new_downstream_addr: peer_addr.clone(),
                        })
                        .await;
                    match notification_sent_res {
                        Ok(_) => {
                            log::info!("Notification requesting latest available template sent successfully to the notifier by a new peer {:?}",peer_addr);
                        }
                        Err(error) => {
                            log::error!("An error occurred while requesting latest template by a newly authorized downstream node - {}",error);
                        }
                    }
                }
                Ok(stratum_response)
            }
            Err(error) => {
                log::error!("{}", error);
                Err(error)
            }
        }
    }
    /// Handles a `mining.submit` request from a downstream miner.
    ///
    /// Validates the submitted share by:
    /// 1. Extracting and parsing worker name, job ID, extranonce2, ntime, and nonce.
    /// 2. Looking up the corresponding mining job from the shared `MiningJobMap`.
    /// 3. Rebuilding the coinbase transaction and computing the updated Merkle root.
    /// 4. Constructing the block header from the submitted values.
    /// 5. Verifying the header against the required PoW target.
    /// # Example Request
    /// ```
    /// use serde_json::json;
    /// let sample_request = json!({"id": 5, "method": "mining.submit",
    ///  "params": [
    ///      "bc1qnp980s5fpp8l94p5cvttmtdqy8rvrq74qly2yrfmzkdsntqzlc5qkc4rkq.bitaxe",
    ///      "2",
    ///      "09000000",
    ///      "6891e02b",
    ///      "91e70222",
    ///      "034ea000"
    ///  ]});
    /// ```
    ///
    /// # Return
    ///  `StratumError` or `Stratum Response`
    pub async fn handle_submit(
        &mut self,
        submit_work_params: &Value,
        mining_job_map: Arc<Mutex<MiningJobMap>>,
        client_request_id: u64,
    ) -> Result<StratumResponses, StratumErrors> {
        let param_array = match submit_work_params.as_array() {
            Some(param_array) => param_array,
            None => {
                return Err(StratumErrors::InvalidMethodParams {
                    method: "mining.submit".to_string(),
                });
            }
        };
        if param_array.len() < 5 {
            return Err(StratumErrors::InvalidMethodParams {
                method: "mining.submit".to_string(),
            });
        }
        let worker_name_res: Result<&str, StratumErrors> = match param_array.get(0) {
            Some(worker_name) => Ok(worker_name.as_str().unwrap()),
            None => Err(StratumErrors::ParamNotFound {
                param: "worker_name".to_string(),
                method: "mining.submit".to_string(),
            }),
        };
        let worker_name = match worker_name_res {
            Ok(name) => name,
            Err(error) => return Err(error),
        };
        log::info!("Worker name connected to the downstream {}", worker_name);
        let job_id_str: &Value = match param_array.get(1) {
            Some(job_id) => job_id,
            None => {
                return Err(StratumErrors::ParamNotFound {
                    param: "job_id".to_string(),
                    method: "mining.submit".to_string(),
                });
            }
        };
        let job_id_str_res = job_id_str
            .as_str()
            .ok_or("Job ID is not a string".to_string())
            .and_then(|s| {
                u64::from_str_radix(s, 16).map_err(|e| format!("Invalid Job ID format: {e}"))
            });
        let job_id = match job_id_str_res {
            Ok(job_id) => job_id,
            Err(error) => {
                return Err(StratumErrors::JobIdCouldNotBeParsed {
                    method: "mining.submit".to_string(),
                    error: error,
                });
            }
        };
        let extranonce2: &str = match param_array.get(2).and_then(|v| v.as_str()) {
            Some(extra) => extra,
            None => {
                return Err(StratumErrors::ParamNotFound {
                    param: "extranonce2".to_string(),
                    method: "mining.submit".to_string(),
                })
            }
        };

        let ntime: &str = match param_array.get(3).and_then(|v| v.as_str()) {
            Some(nt) => nt,
            None => {
                return Err(StratumErrors::ParamNotFound {
                    param: "ntime".to_string(),
                    method: "mining.submit".to_string(),
                })
            }
        };

        let nonce: &str = match param_array.get(4).and_then(|v| v.as_str()) {
            Some(n) => n,
            None => {
                return Err(StratumErrors::ParamNotFound {
                    param: "nonce".to_string(),
                    method: "mining.submit".to_string(),
                })
            }
        };
        //Acquiring lock on the mining map and fetching the submitted job from the memory
        let mut job_mapping = mining_job_map.lock().await;
        let job_r = job_mapping.get_mining_job(job_id).await;
        let submitted_job = match job_r {
            Ok(job) => job,
            Err(error) => {
                return Err(error);
            }
        };
        //Building the coinbase and then eventually the block and testing for the validation against the
        //mainnet/regtest/cpunet/testnet difficulty or the weakshare local difficulty .
        let extranonce_1_hex = hex::encode(self.extranonce1.clone());
        //Reconstructing the entire coinbase with miner submission and extranonce 1
        let coinbase_tx_hex = format!(
            "{}{}{}{}",
            submitted_job.coinbase1,
            extranonce_1_hex,
            extranonce2.to_ascii_lowercase(),
            submitted_job.coinbase2
        );
        let coinbase_bytes = hex::decode(coinbase_tx_hex).unwrap();

        // Log the coinbase transaction in hex
        log::info!("Coinbase transaction hex: {}", hex::encode(&coinbase_bytes));

        let mut coinbase_cursor = Cursor::new(coinbase_bytes);
        let mut coinbase_tx: Transaction =
            bitcoin::Transaction::consensus_decode(&mut coinbase_cursor).unwrap();

        //computing merkle new merkle path due to updated coinbase transaction
        let mut merkel_branches_bytes: Vec<Vec<u8>> = Vec::new();
        for merkel_branch in submitted_job.coinbase_merkel_path.clone() {
            let mut merkel_branch_bytes: [u8; 32] = [0u8; 32];
            //Computing hex of merkel branch in big-endian as expected by the miner
            hex::decode_to_slice(merkel_branch, &mut merkel_branch_bytes).unwrap();
            merkel_branches_bytes.push(Vec::from(merkel_branch_bytes));
        }
        let merkel_root_bytes =
            calculate_merkle_root(coinbase_tx.compute_txid(), merkel_branches_bytes.as_slice());
        //Computing the newly constructed merkle root via the merkle path
        let merkle_root = TxMerkleNode::from_byte_array(merkel_root_bytes);

        //Applying version mask received during mining.configure
        // Job version
        let header_version =
            bitcoin::block::Version::to_consensus(submitted_job.blocktemplate.version.clone());
        let mut final_masked_version =
            bitcoin::block::Version::to_consensus(submitted_job.blocktemplate.version);
        if param_array.len() >= 6 {
            //rolling the version bits only if they have been supplied during the configuration phase
            let rolled_version_bits: &str = match param_array.get(5).and_then(|v| v.as_str()) {
                Some(n) => n,
                None => {
                    return Err(StratumErrors::ParamNotFound {
                        param: "rolled_version".to_string(),
                        method: "mining.submit".to_string(),
                    })
                }
            };
            // Miner received version
            let mut rolled_version = [0u8; 4];
            match hex::decode_to_slice(rolled_version_bits, &mut rolled_version) {
                Ok(_) => (),
                Err(e) => {
                    log::error!("Failed to decode rolled_version_bits: {:?}", e);
                    return Err(StratumErrors::VersionRollingHexParseError {
                        error: e.to_string(),
                    });
                }
            }
            let version_bits = i32::from_be_bytes(rolled_version);

            // Mask set during mining.configure
            let mut mask_bytes = [0u8; 4];
            let version_rolling_mask =
                match self.version_rolling_mask.clone().unwrap().parse::<u32>() {
                    Ok(version_mask) => version_mask,
                    Err(error) => {
                        return Err(StratumErrors::ParsingVersionMask {
                            error: error.to_string(),
                        });
                    }
                };

            let version_rolling_mask_bytes = version_rolling_mask.to_be_bytes();
            let version_rolling_mask_hex = hex::encode(version_rolling_mask_bytes);

            log::info!("Converted version mask --- {:?}", version_rolling_mask_hex);

            match hex::decode_to_slice(version_rolling_mask_hex, &mut mask_bytes) {
                Ok(_) => (),
                Err(e) => {
                    log::error!("Failed to decode version_rolling_mask_hex: {:?}", e);
                    return Err(StratumErrors::VersionRollingHexParseError {
                        error: e.to_string(),
                    });
                }
            }
            let mask_version_bits = i32::from_be_bytes(mask_bytes);
            let precondition = version_bits & !mask_version_bits;
            if precondition != 0 {
                return Err(StratumErrors::MaskNotValid {
                    error: "version_bits & !mask_version_bits must be equal to Zero".to_string(),
                });
            }
            //According to BIP 310 can be seen from extended configurations to downstream during mining.configure
            final_masked_version =
                (header_version & !mask_version_bits) | (version_bits & mask_version_bits);
        }
        //Computing the block header
        let header = BlockHeader {
            version: bitcoin::blockdata::block::Version::from_consensus(final_masked_version),
            prev_blockhash: submitted_job.blocktemplate.previousblockhash,
            merkle_root: merkle_root,
            time: BlockTime::from_u32(u32::from_str_radix(ntime, 16).unwrap()),
            bits: submitted_job.blocktemplate.bits,
            nonce: u32::from_str_radix(nonce, 16).unwrap(),
        };
        let compact_target = submitted_job.blocktemplate.bits;
        let target = bitcoin::Target::from_compact(compact_target);
        log::info!("target    : {}", target.to_hex());
        log::info!(
            "block_hash: {}",
            hex::encode(header.block_hash().to_byte_array())
        );

        // Print each header field in big-endian hex just before PoW validation
        let coinbase_txid_be_hex = hex::encode(coinbase_tx.compute_txid().to_byte_array());
        let version_be_hex = {
            let v = header.version.to_consensus() as u32;
            hex::encode(v.to_be_bytes())
        };
        let prevhash_be_hex = hex::encode(header.prev_blockhash.to_byte_array());
        let merkle_root_be_hex = hex::encode(header.merkle_root.to_byte_array());
        let time_be_hex = hex::encode(header.time.to_u32().to_be_bytes());
        let bits_be_hex = hex::encode(header.bits.to_consensus().to_be_bytes());
        let nonce_be_hex = hex::encode(header.nonce.to_be_bytes());

        log::info!("coinbase_txid: {}", coinbase_txid_be_hex);
        log::info!("header.version: {}", version_be_hex);
        log::info!("header.prev_blockhash: {}", prevhash_be_hex);
        log::info!("header.merkle_root: {}", merkle_root_be_hex);
        log::info!("header.time: {}", time_be_hex);
        log::info!("header.bits: {}", bits_be_hex);
        log::info!("header.nonce: {}", nonce_be_hex);
        //Pushing back the witness comittment
        let witness = submitted_job
            .coinbase_witness_commitment
            .clone()
            .unwrap()
            .to_vec();
        let witness_bytes = witness.get(0);
        coinbase_tx
            .inputs_mut()
            .get_mut(0)
            .unwrap()
            .witness
            .push(witness_bytes.unwrap());
        let mut block_transactions = vec![coinbase_tx];
        block_transactions.extend(submitted_job.blocktemplate.transactions.clone());

        // Construct and log the complete block using rust-bitcoin's Block struct
        let complete_block = bitcoin::Block::new_unchecked(header, block_transactions);

        let complete_block_bytes = bitcoin::consensus::serialize(&complete_block);
        log::info!("Complete block hex: {}", hex::encode(&complete_block_bytes));
        log::info!(
            "block_hash: {}",
            hex::encode(complete_block.block_hash().to_byte_array())
        );

        //Checking with PoW of the target whether the block sent by downstream is below that or not
        match header.validate_pow(target) {
            Ok(_) => log::info!("Header meets the target"),
            Err(e) => {
                log::info!("Header does not meet the target: {}", e);

                return Ok(StratumResponses::StandardResponse {
                    std_response: StandardResponse::new_ok(Some(client_request_id), json!(false)),
                });
            }
        }

        Ok(StratumResponses::StandardResponse {
            std_response: StandardResponse::new_ok(Some(client_request_id), json!(true)),
        })
    }
    /// Processes a `mining.set_difficulty` request from the client.
    ///
    /// Attempts to read a new difficulty value from the first element of the
    /// provided `suggest_difficulty_params` JSON array. The value must be a valid `u64`.
    ///
    ///  # Arguments
    /// * `suggest_difficulty_params` – JSON array of method parameters, expected format: `[new_difficulty]`.
    ///  # Returns
    /// * `Ok(StratumResponses::SuggestDifficultyResponse)` with the parsed difficulty value.
    /// * `Err(StratumErrors::InvalidMethodParams)` if the parameter is missing or not a `u64`.
    pub async fn suggest_difficulty(
        &mut self,
        suggest_difficulty_params: &Value,
    ) -> Result<StratumResponses, StratumErrors> {
        if let Some(difficulty) = suggest_difficulty_params.get(0) {
            log::info!(
                "Handling suggested difficulty - {}",
                suggest_difficulty_params
            );
            self.suggest_difficulty_done = true;
            Ok(StratumResponses::SuggestDifficultyResponse {
                suggest_difficulty_resp: SuggestDifficultyResponse {
                    method: "mining.set_difficulty".to_string(),
                    params: vec![difficulty.as_u64().unwrap()],
                },
            })
        } else {
            return Err(StratumErrors::InvalidMethodParams {
                method: "mining.set_difficulty".to_string(),
            });
        }
    }
    ///The result from an authorize request is usually true (successful), or false. The password may be omitted if the server does not require passwords.
    /// Handles the `mining.authorize` request from a downstream client.
    ///
    /// This method attempts to extract a username and password from the incoming
    /// JSON parameters array. If both values are present and valid, the client is
    /// marked as authorized and a positive (`true`) `StandardResponse` is returned.
    /// # Returns
    /// * `Ok(StratumResponses::StandardResponse)` with `true` if authorization succeeds.
    /// * `Err(StratumErrors::InvalidMethodParams)` if either parameter is missing or invalid.
    pub async fn handle_authorize(
        &mut self,
        authorize_request_params: &Value,
        client_request_id: u64,
    ) -> Result<StratumResponses, StratumErrors> {
        log::info!(
            "Authorization is taking place -- {:?}",
            authorize_request_params
        );
        let param_array = match authorize_request_params.as_array() {
            Some(param_array) => param_array,
            None => {
                return Err(StratumErrors::InvalidMethodParams {
                    method: "mining.authorize".to_string(),
                });
            }
        };
        let username_res: Result<&str, StratumErrors> = match param_array.get(0) {
            Some(user) => Ok(user.as_str().unwrap()),
            None => {
                return Err(StratumErrors::ParamNotFound {
                    param: "username".to_string(),
                    method: "mining.authorize".to_string(),
                });
            }
        };
        let username = match username_res {
            Ok(username_value) => username_value,
            Err(error) => {
                return Err(error);
            }
        };
        let password_res: Result<&str, StratumErrors> = match param_array.get(1) {
            Some(pass) => Ok(pass.as_str().unwrap()),
            None => Err(StratumErrors::ParamNotFound {
                param: "password".to_string(),
                method: "mining.authorize".to_string(),
            }),
        };

        let password = match password_res {
            Ok(password_value) => password_value,
            Err(error) => {
                return Err(error);
            }
        };
        self.authorized = true;
        log::info!("username {}, password {}", username, password);
        Ok(StratumResponses::StandardResponse {
            std_response: (StandardResponse {
                id: Some(client_request_id),
                result: Some(json!(true)),
                error: None,
            }),
        })
    }
    /// Handle the "mining.configure" message ) which handles the initial configuration/negotiation of features in a generic way. So that adding features in the future can be done without a necessity to add new messages to stratum protocol. as per introduced in BIP 310 - https://en.bitcoin.it/wiki/BIP_0310#Request_%22mining.configure%22 .
    ///
    /// Currently, the following extensions are defined:
    // "version-rolling"
    // "minimum-difficulty"
    // "subscribe-extranonce"
    pub async fn handle_configure(
        &mut self,
        config_req_params: &Value,
        client_request_id: u64,
    ) -> Result<StratumResponses, StratumErrors> {
        log::info!(
            "{:?} configuration handling is taking place",
            config_req_params
        );
        let params = match config_req_params.as_array() {
            Some(param_array) => param_array,
            None => {
                return Err(StratumErrors::InvalidMethodParams {
                    method: "mining.configure".to_string(),
                });
            }
        };
        if params.len() != 2 {
            return Err(StratumErrors::InvalidMethodParams {
                method: "mining.configure".to_string(),
            });
        }

        let features = match params[0].as_array() {
            Some(feature_arr) => feature_arr,
            None => {
                return Err(StratumErrors::ParamNotFound {
                    param: "feature_array".to_string(),
                    method: "mining.configure".to_string(),
                })
            }
        };
        let feature_names: Vec<String> = match features
            .iter()
            .map(|f| f.as_str().map(|s| s.to_string()))
            .collect::<Option<Vec<String>>>(){
                Some(feature_arr)=>feature_arr,
                None=>{
                    return Err(StratumErrors::ConfigureFeatureStringConversion { error: "Json value could not be converted to string in while handling mining.configure ".to_string() })
                }
            };
        log::info!("{:?}", feature_names);
        let config_map = match params[1].as_object() {
            Some(con_map) => con_map,
            None => {
                return Err(StratumErrors::ParamNotFound {
                    param: "configuration_map".to_string(),
                    method: "mining.config".to_string(),
                });
            }
        };
        log::info!("{:?}", config_map);
        //Possible `req_params` under the request sent to server via client
        #[allow(unused)]
        let minimum_difficulty = config_map.get("minimum-difficulty.value").or(None);
        //Rollable version bits required by downstream
        let version_rolling_mask = config_map.get("version-rolling.mask").or(None);
        //Minimum bits rollable of version
        let version_rolling_min_bit_count =
            config_map.get("version-rolling.min-bit-count").or(None);
        if version_rolling_mask.is_none() == false {
            let mut mask_bytes: [u8; 4] = [0u8; 4];
            let version_rolling_mask_str = match version_rolling_mask.unwrap().as_str() {
                Some(version_str) => version_str,
                None => {
                    return Err(StratumErrors::VersionRollingStringParseError {
                        error: "Version rolling mask could not be converted to string from provided bytes".to_string(),
                    });
                }
            };
            match hex::decode_to_slice(version_rolling_mask_str, &mut mask_bytes) {
                Ok(_) => {}
                Err(error) => {
                    return Err(StratumErrors::VersionRollingHexParseError {
                        error: error.to_string(),
                    });
                }
            };
            //Intersecting with the bits provided by the pool and miner's suggested one
            let final_rollable_version_bits = u32::from_be_bytes(mask_bytes) & 0x1FFFE000;
            // `0x1FFFE000` is a reasonable default as it allows all 16 version bits to be used
            let hex_str = u32::to_string(&final_rollable_version_bits);
            self.version_rolling_mask = Some(hex_str);
        }
        if version_rolling_min_bit_count.is_none() == false {
            let mut mask_bytes: [u8; 4] = [0u8; 4];
            let version_rolling_min_bit_count_str =
                version_rolling_min_bit_count.unwrap().as_str().unwrap();
            match hex::decode_to_slice(version_rolling_min_bit_count_str, &mut mask_bytes) {
                Ok(_) => {}
                Err(error) => {
                    return Err(StratumErrors::VersionrollingMinBitCountHexParseError {
                        error: error.to_string(),
                    });
                }
            };
            self.version_rolling_min_bit = Some(u32::from_be_bytes(mask_bytes));
        }
        self.channel_configured = true;
        Ok(StratumResponses::StandardResponse {
            std_response: StandardResponse {
                id: Some(client_request_id),
                result: Some(json!({
                    "minimum-difficulty":false,
                    "version-rolling": true,
                    "version-rolling.mask":self.version_rolling_mask.clone().unwrap_or("1fffe000".to_string()),
                    "version-rolling.min-bit-count":self.version_rolling_min_bit.unwrap_or(0)

                })),
                error: None,
            },
        })
    }
    /// Handles the `mining.subscribe` request as per the Stratum protocol specification.
    ///
    /// This request is used by a mining client to subscribe to a Stratum server
    /// and obtain session-specific identifiers for further communication.
    /// Optionally, the client may pass a subscription ID to resume a previous
    /// session, potentially reusing the same `extranonce1`.
    /// # Request Format
    /// ```json
    /// ["<optional-subscription-id>"]
    /// ```
    ///
    /// # Response Format
    /// Returns a JSON array containing:
    /// 1. **Subscriptions** – An array of `(method, subscription_id)` tuples defining active subscriptions.
    /// 2. **ExtraNonce1** – Hex-encoded, per-connection unique string used in coinbase transaction construction.
    /// 3. **ExtraNonce2_size** – The number of bytes reserved for the client's `ExtraNonce2` counter.
    ///
    /// Example Response:
    /// ```json
    /// [
    ///   [["mining.set_difficulty", "34"], ["mining.notify", "12"]],
    ///   "1a2b3c4d",
    ///   16
    /// ]
    /// ```
    pub async fn handle_subscribe(
        &mut self,
        subscribe_req_params: &Value,
        client_request_id: u64,
    ) -> Result<StratumResponses, StratumErrors> {
        log::info!("Subscribing is taking place -- {:?}", subscribe_req_params);
        //TODO: dummy testing subscription IDs must be unique though can be changed accordingly these are just dummy values
        let subscriptions: Vec<(String, String)> = vec![
            (String::from("mining.set_difficulty"), String::from("34")),
            (String::from("mining.notify"), String::from("12")),
        ];
        self.subscribed = true;
        /* 16 is the default since that is the only value the
         * pool supports currently  As per SV2 */
        let extranonce1_hex_str = hex::encode(self.extranonce1.clone());
        Ok(StratumResponses::StandardResponse {
            std_response: StandardResponse::new_ok(
                Some(client_request_id),
                json!([subscriptions, extranonce1_hex_str, self.extranonce2_len]),
            ),
        })
    }
}

impl Default for DownstreamClient {
    fn default() -> Self {
        //ExtraNonce1. - Hex-encoded, per-connection unique string which will be used for creating generation transactions later.
        //4 bytes
        let mut extranonce1_bytes = [0; 4];
        rand::thread_rng().fill_bytes(&mut extranonce1_bytes);
        log::info!(
            "Extranonce1 generated for a new downstream connection is following {:?}",
            hex::encode(&extranonce1_bytes)
        );
        DownstreamClient {
            authorized: false,
            downstream_ip: "0.0.0.0".to_string(),
            subscribed: false,
            suggest_difficulty_done: false,
            channel_configured: false,
            //generating a random u32 client connection id
            connection_id: rand::thread_rng().next_u32(),
            extranonce1: Vec::from(extranonce1_bytes),
            version_rolling_mask: None,
            version_rolling_min_bit: None,
            extranonce2_len: EXTRANONCE2_SIZE,
            monitor_target: None,
        }
    }
}
/// Represents the Stratum server instance, which maintains configuration
/// and manages downstream client connections.
///
/// # Fields
/// * `stratum_config` - The configuration settings for the Stratum server.
/// * `downstream_connection_mapping` - Thread-safe mapping of downstream
///   miner connections, wrapped in `Arc<Mutex<...>>` to allow concurrent access
///   across async tasks and threads.
#[derive(Debug)]
pub struct Server {
    stratum_config: StratumServerConfig,
    downstream_connection_mapping: Arc<Mutex<ConnectionMapping>>,
}
///Types for the `mining.notify` jobs to be sent to the fellow connected downstream nodes
/// `SendToAll` broadcasts the most recently received `job` to the downstream nodes .
/// `SendLatestTemplateToNewDownstream` sends the latest available template to the most recent connected node so that
/// it can start working as soon as it is connected to the stratum service via `braidpool` .
pub enum NotifyCmd {
    SendToAll {
        template: BlockTemplate,
        merkle_branch_coinbase: Vec<Vec<u8>>,
    },
    SendLatestTemplateToNewDownstream {
        new_downstream_addr: String,
    },
}
/// Represents a `mining.notify` job message in the Stratum protocol.
///
/// This struct contains all the parameters sent by the mining pool to a miner
/// when a new mining job is assigned. Miners use these values to construct
/// a candidate block header and start hashing.
///
/// # Fields
/// - `job_id` — Unique identifier for the mining job.
/// - `prevhash` — Hash of the previous block header (in reversed byte order).
/// - `coinbase1` — First half of the coinbase transaction before the extranonce.
/// - `coinbase2` — Second half of the coinbase transaction after the extranonce.
/// - `merkle_branches` — List of Merkle branches used to compute the Merkle root.
/// - `version` — Block version in hex.
/// - `nbits` — Compact target representation in hex.
/// - `ntime` — Current time in seconds since epoch (in hex).
/// - `clean_jobs` — If `true`, miner should drop all previous jobs and start fresh.
#[derive(Debug, Clone, Deserialize, Serialize)]
pub struct JobNotification {
    pub job_id: String,
    pub prevhash: String,
    pub coinbase1: String,
    pub coinbase2: String,
    pub merkle_branches: Vec<String>,
    pub version: String,
    pub nbits: String,
    pub ntime: String,
    pub clean_jobs: bool,
    pub coinbase_witness_commitment: Option<Witness>,
}
///`JobDetails` which are required for tracking of the jobs available to each downstream node
/// which is required during the job validation during `mining.submit` from the downstream node .
#[derive(Debug, Clone)]
pub struct JobDetails {
    pub blocktemplate: BlockTemplate,
    pub coinbase1: String,
    pub coinbase2: String,
    pub coinbase_merkel_path: Vec<String>,
    pub coinbase_witness_commitment: Option<Witness>,
}
///Struct storing all the jobs mapped accroding to the job id
/// it will serve the purpose for maintaining the details received from the downstream as well as other
/// jobs that is required for reconstruction of the `Bead` or `WeakShare` according to the values received from the
/// downstream nodes .
///Declaring as `Arc` object for shared reference across different tasks due to
/// multiple threads serving requests according to the new process of serving requests .
pub struct MiningJobMap {
    mining_jobs: HashMap<u64, JobDetails>,
    latest_job_id: u64,
}
impl MiningJobMap {
    pub fn new() -> Self {
        Self {
            mining_jobs: HashMap::new(),
            latest_job_id: 0,
        }
    }
    ///Inserting a suitable mining job which has been passed to the downstream being constructed from a suitable block template .
    pub async fn insert_mining_job(&mut self, job_details: JobDetails) {
        log::info!(
            "Inserting new mining job with job_id: {}",
            self.latest_job_id + 1
        );
        self.mining_jobs.insert(self.latest_job_id + 1, job_details);
        self.latest_job_id += 1;
    }
    ///Getting a mining job from the existing jobs upto a given timestamp t used by the downstream node for mining
    ///
    /// also served as the response for mining.getjob method from client2server in stratum .
    pub async fn get_mining_job(&mut self, job_id: u64) -> Result<&JobDetails, StratumErrors> {
        log::info!("Retrieving mining job with job_id: {}", job_id);
        if let Some(current_job) = self.mining_jobs.get(&job_id) {
            Ok(current_job)
        } else {
            log::warn!("Mining job with id {} not found", job_id);
            Err(StratumErrors::MiningJobNotFound { job_id: job_id })
        }
    }
    /// Get the next job id to be used while constructing `Jobs` from the `templates` received via IPC
    pub fn get_next_job_id(&mut self) -> u64 {
        log::info!("Generated next job_id: {}", self.latest_job_id);
        self.latest_job_id + 1
    }
}
///`Notifier` that will serve the purpose of notifying the downstream nodes with the lates available jobs
/// for mining to take place via `mining.notify`.
///
pub struct Notifier {
    ///`IpcGBT` notification receiver whenever new `template` is fethced or tip is updated .
    notification_receiver: mpsc::Receiver<NotifyCmd>,
    ///`JobMap` associated with each `peer_addr` and the jobs associated with it .
    pub job_map_arc: Arc<Mutex<HashMap<String, Arc<Mutex<MiningJobMap>>>>>,
}
///Since the prev_block_hash received in `gbt` is in BigEndian format it must be converted to `Little endian`.
fn to_little_endian(hex_str: &str) -> String {
    hex_str
        .as_bytes()
        .chunks(2)
        .map(|chunk| std::str::from_utf8(chunk).unwrap())
        .rev()
        .collect::<Vec<&str>>()
        .join("")
}
///Since the prev_block_hash received in `gbt` is in BigEndian format it must be converted to `Little endian`.
pub fn reverse_four_byte_chunks(hash_hex: &str) -> Result<String, StratumErrors> {
    if hash_hex.len() != 64 {
        return Err(StratumErrors::PrevHashNotReversed {
            error: "Hash length is incorrect".to_string(),
        });
    }
    let bytes = hex::decode(hash_hex).unwrap();
    // Reverse the byte order in 4-byte chunks
    let mut reversed_bytes = Vec::with_capacity(bytes.len());
    for chunk in bytes.chunks(4).rev() {
        reversed_bytes.extend_from_slice(chunk);
    }

    Ok(hex::encode(reversed_bytes))
}
impl Notifier {
    ///Spawning a new notifier instance .
    pub fn new(
        notification_rx: mpsc::Receiver<NotifyCmd>,
        job_map_arc: Arc<Mutex<HashMap<String, Arc<Mutex<MiningJobMap>>>>>,
    ) -> Self {
        Self {
            notification_receiver: notification_rx,
            job_map_arc: job_map_arc,
        }
    }
    ///Constructing the mining.notify template following the corrsponding attributes to be sent as a job to the downstream miner for
    ///mining to take place .
    ///
    /// **Job ID**. This is included when miners submit a results so work can be matched with proper transactions.
    ///
    /// **Hash of previous block**. Used to build the header.
    ///
    /// **Generation transaction (part 1)**. The miner inserts ExtraNonce1 and ExtraNonce2 after this section of the transaction data.
    ///
    /// **Generation transaction (part 2)**. The miner appends this after the first part of the transaction data and the two ExtraNonce values.
    ///
    /// **List of merkle branches**. The generation transaction is hashed against the merkle branches to build the final merkle root.
    ///
    /// **Bitcoin block version**. Used in the block header.
    ///
    /// **nBits**. The encoded network difficulty. Used in the block header.
    ///
    /// **nTime**. The current time. nTime rolling should be supported, but should not increase faster than actual time.
    ///
    /// **Clean Jobs**. If true, miners should abort their current work and immediately use the new job, even if it degrades hashrate in the short term. If false, they can still use the current job, but should move to the new one as soon as possible without impacting hashrate.
    pub async fn construct_job_notification(
        clean_job: bool,
        mut notified_template: BlockTemplate,
        new_job_id: u64,
        merkle_coinbase_branch: Vec<Vec<u8>>,
    ) -> Result<JobNotification, StratumErrors> {
        log::info!(
            "Constructing JobNotification for job_id: {} with clean_job: {}",
            new_job_id,
            clean_job
        );

        let coinbase_transaction = notified_template.transactions.get_mut(0).unwrap();
        let coinbase_witness_commitment = coinbase_transaction
            .inputs()
            .get(0)
            .unwrap()
            .witness
            .clone();
        if let Some(input) = coinbase_transaction.inputs_mut().get_mut(0) {
            input.witness.clear();
        };
        let deserialized_coinbase = serialize::<Transaction>(&coinbase_transaction);
        log::info!(
            "Deserialized coinbase length is - {:?} \n and the coinbase tx is - {:?}",
            deserialized_coinbase.len(),
            coinbase_transaction
        );
        //For splitting of the coinbase we check for the extranonce_seperator we had inserted while reconstructing the coinbase during the
        //fetching of the template via IPC .
        let separator_pos = match deserialized_coinbase
            .as_slice()
            .windows(EXTRANONCE1_SIZE + EXTRANONCE2_SIZE)
            .position(|window| window == EXTRANONCE_SEPARATOR)
        {
            Some(pos) => pos,
            None => return Err(StratumErrors::InvalidCoinbase),
        };
        let coinbase_1 = hex::encode(&deserialized_coinbase[..separator_pos]);
        let coinbase_2 = hex::encode(
            &deserialized_coinbase[separator_pos + (EXTRANONCE1_SIZE + EXTRANONCE2_SIZE)..],
        );
        log::info!("Coinbase splitted with coinbase_prefix and coinbase suffix respectively as -- {:?} {:?}",coinbase_1,coinbase_2);
        //Constructing merkel root via merkel path .
        let mut merkle_branches: Vec<String> = Vec::new();
        let mut txids_hashes: Vec<Txid> = vec![];
        for tx in notified_template.transactions {
            txids_hashes.push(tx.compute_txid());
        }
        if merkle_coinbase_branch.len() == 0 {
            log::info!("Empty branch hence previous template was being used and hence saving has to be done !");
        } else {
            for sibling_node in merkle_coinbase_branch.iter() {
                let sibling_hex = hex::encode(sibling_node);
                merkle_branches.push(sibling_hex);
            }
        }
        log::info!(
            "merkle branches for the given template's coinbase are respectively - {:?}",
            merkle_branches
        );
        //Stratum accepts the prev block hash to be in little endian instead of big endian
        //therefore byte by byte reversal is required here .
        let prev_block_hash = notified_template.previousblockhash.to_string();
        let prev_block_hash_little_endian = match reverse_four_byte_chunks(prev_block_hash.as_str())
        {
            Ok(reversed_hash) => reversed_hash,
            Err(error) => {
                return Err(error);
            }
        };
        log::info!(
            "Converting the prev block hash to little endian done -- {:?}",
            prev_block_hash_little_endian
        );
        let bitcoin_block_version = notified_template.version.to_consensus();
        let bits = notified_template.bits;
        let time = notified_template.curtime.to_u32();
        //Adding support for segwit coinbase
        Ok(JobNotification {
            job_id: new_job_id.to_string(),
            prevhash: prev_block_hash_little_endian,
            coinbase1: coinbase_1,
            coinbase2: coinbase_2,
            merkle_branches: merkle_branches,
            //converting the i32 version to hex string
            version: hex::encode(bitcoin_block_version.to_be_bytes()),
            //String is acceptable
            nbits: format!("{:08x}", bits.to_consensus()),
            //ntime is to be hex encoded
            ntime: hex::encode(time.to_be_bytes()),
            clean_jobs: clean_job,
            coinbase_witness_commitment: Some(coinbase_witness_commitment),
        })
    }
    /// Runs the Stratum notifier task that handles broadcasting mining jobs to downstream miners.
    ///
    /// This asynchronous function continuously listens for notification commands and performs
    /// one of the following actions:
    /// 1. **Broadcast a new template to all connected miners**:
    ///    - Constructs a new mining job from the latest `BlockTemplate`.
    ///    - Updates the `JobMap` for each downstream connection with the new job details.
    ///    - Serializes the `JobNotification` and sends it to each miner via their respective channels.
    /// 2. **Send the latest available template to a newly connected miner**:
    ///    - Constructs a mining job from the current latest template.
    ///    - Updates the `JobMap` for the newly authorized and subscribed miner.
    ///    - Sends the serialized `JobNotification` to the new miner's channel.
    ///
    /// # Returns
    /// * `Ok(())` on successful completion (runs indefinitely unless an error occurs).
    /// * `Err(StratumErrors)` if an error occurs while constructing or sending a job notification.
    ///
    pub async fn run_notifier(
        &mut self,
        downstream_connection_map: Arc<Mutex<ConnectionMapping>>,
        latest_template_arc: &mut Arc<Mutex<BlockTemplate>>,
        latest_template_merkle_branch_arc: &mut Arc<Mutex<Vec<Vec<u8>>>>,
    ) -> Result<(), StratumErrors> {
        log::info!("Notifier task has  started");
        while let Some(notification_command) = self.notification_receiver.recv().await {
            match notification_command {
                //Whenever a new template is received it is broadcasted across all the downstream nodes connected .
                NotifyCmd::SendToAll {
                    template,
                    merkle_branch_coinbase,
                } => {
                    log::info!("Received new template to broadcast to all clients");
                    let mut template_ref = template.clone();
                    //We will receive the template from the IPC channel and construct a valid job
                    //from the provided template and pass onto the message_reciver in the handle connection for
                    // downstream communication to take place.
                    for (peer_adr, mining_job_arc) in self.job_map_arc.lock().await.iter() {
                        let mut curr_peer_mining_job_map = mining_job_arc.lock().await;
                        //The new job id to be provided while constructing the new job .
                        let next_job_id = curr_peer_mining_job_map.get_next_job_id();
                        //Clean Jobs. If true, miners should abort their current work and immediately use the new job, even if it degrades hashrate in the short term. If false, they can still use the current job, but should move to the new one as soon as possible without impacting hashrate.
                        let clean_job = false;
                        let job_notification = Self::construct_job_notification(
                            clean_job,
                            template_ref.clone(),
                            next_job_id,
                            merkle_branch_coinbase.clone(),
                        )
                        .await;
                        let serialized_notification: Result<String, StratumErrors> =
                            match job_notification {
                                Ok(job) => {
                                    log::info!(
                                        "Successfully constructed job notification for job_id {}",
                                        next_job_id
                                    );
                                    //Updating the existing `JobMap` with the new job constructed from the newly generated
                                    //template received from IPC .
                                    //Removing the stale coinbase
                                    template_ref.transactions.remove(0);
                                    let job_details = JobDetails {
                                        blocktemplate: template_ref.clone(),
                                        coinbase1: job.coinbase1.clone(),
                                        coinbase2: job.coinbase2.clone(),
                                        coinbase_merkel_path: job.merkle_branches.clone(),
                                        coinbase_witness_commitment: job
                                            .coinbase_witness_commitment,
                                    };
                                    curr_peer_mining_job_map
                                        .insert_mining_job(job_details)
                                        .await;
                                    //Constructing Server2Client response.
                                    let job_notification_response = JobNotificationResponse {
                                        method: "mining.notify".to_string(),
                                        params: json!([
                                            job.job_id,
                                            job.prevhash,
                                            job.coinbase1,
                                            job.coinbase2,
                                            job.merkle_branches,
                                            job.version,
                                            job.nbits,
                                            job.ntime,
                                            job.clean_jobs
                                        ]),
                                    };
                                    Ok(serde_json::to_string(&job_notification_response).unwrap())
                                }
                                Err(error) => Err(error),
                            };
                        let job_notification = match serialized_notification {
                            Ok(job) => job,
                            Err(error) => {
                                log::error!(
                                    "Error occurred while fetching the job notification - {}",
                                    error
                                );
                                return Err(error);
                            }
                        };
                        //Sending the notification for broadcasting it across all the downstream
                        //nodes that is write to `TcpStream` .
                        let downstream_channel_mapping = downstream_connection_map
                            .lock()
                            .await
                            .downstream_channel_mapping
                            .clone();
                        //Fetching the downstream miner message sender via the `[Connection Mapping]`
                        if let Some(downstream_channel) = downstream_channel_mapping.get(peer_adr) {
                            log::info!("Sending template to downstream at address {}", peer_adr);
                            #[allow(unused)]
                            let msg_sent_result =
                                match downstream_channel.send(job_notification.clone()).await {
                                    Ok(_) => {}
                                    Err(error) => {
                                        return Err(StratumErrors::NotifyMessageNotSent {
                                            error: error.to_string(),
                                            msg: error.0,
                                            msg_type: "SendToAll".to_string(),
                                        })
                                    }
                                };
                        }
                    }
                }
                //Another notification event to provide the latest possible template available whenever a new peer
                // is connected `subscribed` and `authorized` via stratum protocol.
                NotifyCmd::SendLatestTemplateToNewDownstream {
                    new_downstream_addr,
                } => {
                    let latest_template = latest_template_arc.lock().await.to_owned();
                    let latest_template_merkle_branch =
                        latest_template_merkle_branch_arc.lock().await.to_owned();
                    let current_downstream_mapping = downstream_connection_map.lock().await;
                    let current_downstream_message_sender_res = current_downstream_mapping
                        .downstream_channel_mapping
                        .get(&new_downstream_addr);
                    let global_peer_mining_job_map_arc = self.job_map_arc.lock().await;
                    let current_peer_mining_job_map_arc = global_peer_mining_job_map_arc
                        .get(&new_downstream_addr)
                        .unwrap();
                    let mut curr_peer_mining_job_map = current_peer_mining_job_map_arc.lock().await;
                    let current_downstream_message_sender =
                        match current_downstream_message_sender_res {
                            Some(downstream_sender) => downstream_sender,
                            None => {
                                log::error!("Newly peer not found in the Connection mapping");
                                return Err(StratumErrors::PeerNotFoundInConnectionMapping {
                                    peer_addr: new_downstream_addr,
                                });
                            }
                        };

                    let next_job_id = curr_peer_mining_job_map.get_next_job_id();
                    //Clean Jobs. If true, miners should abort their current work and immediately use the new job, even if it degrades hashrate in the short term. If false, they can still use the current job, but should move to the new one as soon as possible without impacting hashrate.
                    let clean_job = false;
                    let job_notification = Self::construct_job_notification(
                        clean_job,
                        latest_template.clone(),
                        next_job_id,
                        latest_template_merkle_branch,
                    )
                    .await;
                    let serialized_notification: Result<String, StratumErrors> =
                        match job_notification {
                            Ok(job) => {
                                log::info!(
                                    "Successfully constructed job notification for job_id {}",
                                    next_job_id
                                );
                                //Updating the existing `JobMap` with the new job constructed from the newly generated
                                //template received from IPC .
                                //Removing stale coinbase
                                let mut latest_template_ref = latest_template.clone();
                                latest_template_ref.transactions.remove(0);
                                let job_details = JobDetails {
                                    blocktemplate: latest_template_ref,
                                    coinbase1: job.coinbase1.clone(),
                                    coinbase2: job.coinbase2.clone(),
                                    coinbase_merkel_path: job.merkle_branches.clone(),
                                    coinbase_witness_commitment: job.coinbase_witness_commitment,
                                };
                                curr_peer_mining_job_map
                                    .insert_mining_job(job_details)
                                    .await;
                                let job_notification_response = JobNotificationResponse {
                                    method: "mining.notify".to_string(),
                                    params: json!([
                                        job.job_id,
                                        job.prevhash,
                                        job.coinbase1,
                                        job.coinbase2,
                                        job.merkle_branches,
                                        job.version,
                                        job.nbits,
                                        job.ntime,
                                        job.clean_jobs
                                    ]),
                                };
                                Ok(serde_json::to_string(&job_notification_response).unwrap())
                            }
                            Err(error) => Err(error),
                        };
                    let job_notification = match serialized_notification {
                        Ok(job) => job,
                        Err(error) => {
                            log::error!(
                                "Error occurred while fetching the job notification - {}",
                                error
                            );
                            return Err(error);
                        }
                    };
                    match current_downstream_message_sender
                        .send(job_notification)
                        .await
                    {
                        Ok(_) => {}
                        Err(error) => {
                            return Err(StratumErrors::NotifyMessageNotSent {
                                error: error.to_string(),
                                msg: error.0,
                                msg_type: "LatestTemplateSent".to_string(),
                            })
                        }
                    };
                }
            }
        }
        Ok(())
    }
}
///Connection information associated with each downstream peer associated along with the mapped `Sender_channel` for sending downstream responses and communication.
#[derive(Debug, Clone)]
pub struct ConnectionMapping {
    downstream_channel_mapping: HashMap<String, mpsc::Sender<String>>,
}
impl ConnectionMapping {
    pub fn new() -> Self {
        ConnectionMapping {
            downstream_channel_mapping: HashMap::new(),
        }
    }
    ///Inserting new connction along with its `peer_socket_address` and `Sender_channel` associated with the client.
    pub fn new_connection(
        &mut self,
        peer_addr: String,
        peer_msg_sender: mpsc::Sender<String>,
    ) -> () {
        self.downstream_channel_mapping
            .insert(peer_addr, peer_msg_sender);
    }
}
//Containing all the functionality for a stratum service
impl Server {
    ///`Spawning` new stratum server along with custom_config or default config .
    pub fn new(
        server_config: StratumServerConfig,
        connection_mapping_arc: Arc<Mutex<ConnectionMapping>>,
    ) -> Self {
        log::info!("Initializing server with config: {:?}", server_config);

        Self {
            stratum_config: server_config,
            downstream_connection_mapping: connection_mapping_arc,
        }
    }
    /// Starts and runs the Stratum server, handling incoming miner connections.
    ///
    /// This asynchronous function continuously listens on the configured hostname and port
    /// for new TCP connections from downstream miners. Each connection is managed in a separate
    /// task, allowing concurrent processing of multiple miners.
    ///
    /// # Returns
    /// * `Ok(())` – Runs indefinitely; returns only if the listener loop is broken or an unrecoverable error occurs.
    /// * `Err(Box<std::io::Error>)` – If binding to the server address fails.
    pub async fn run_stratum_service(
        &mut self,
        mining_job_map: Arc<Mutex<HashMap<String, Arc<Mutex<MiningJobMap>>>>>,
        notification_sender: mpsc::Sender<NotifyCmd>,
    ) -> Result<(), Box<std::io::Error>> {
        log::info!("Server is being started");
        let bind_address = format!(
            "{}:{}",
            self.stratum_config.hostname, self.stratum_config.port
        );
        log::info!("Server is listening at {:?}", bind_address);
        let listener = match TcpListener::bind(&bind_address).await {
            Ok(listener) => listener,
            Err(e) => {
                log::error!("Failed to bind to {}: {}", bind_address, e);
                return Err(Box::new(e));
            }
        };
        loop {
            tokio::select! {
                event = listener.accept()=>{
                    //shared ownership across all tasks and spawning a seperate downstream for each new connection
                    let self_ = Arc::new(Mutex::new(DownstreamClient::default()));
                    //downstream miner mapping for associated jobs for a specific channel for downstream
                    let self_mining_map = Arc::new(Mutex::new(MiningJobMap::new()));
                    match event{
                        Ok((stream,peer_addr))=>{
                            let (reader, writer) = stream.into_split();
                            //Notification sender to the `Notifier` task
                            let notification_sender = notification_sender.clone();
                            //Adding the downstream mining map to global mapper
                            mining_job_map.lock().await.insert(peer_addr.to_string(), self_mining_map.clone());
                            //downstream channel for server2client communication to take place
                            let (downstream_tx,mut downstream_rx) = mpsc::channel(1024);
                            //adding the new connection to the connection map
                            self.downstream_connection_mapping.lock().await.new_connection(peer_addr.to_string(), downstream_tx.clone());
                            log::info!("Connection established from a downstream node with peer address - {:?}",peer_addr);
                            self_.lock().await.downstream_ip = peer_addr.to_string();
                            //catering each new connection as seperate process
                             tokio::spawn(async move{
                              let _=  Self::handle_connection(self_.clone(),peer_addr,reader,writer,&mut downstream_rx,self_mining_map.clone(),downstream_tx,notification_sender).await;
                             });
                        }
                        Err(error)=>{
                            log::info!("Connection failed: {:?}", error);
                        }
                    }
                }
            }
        }
    }
    /// Handles an individual downstream miner connection over TCP.
    ///
    /// This function manages both reading requests from the miner and sending server messages or job
    /// notifications back to the miner. Each connection runs in its own asynchronous task, enabling
    /// concurrent handling of multiple miners.
    ///
    /// # Functionality
    /// 1. Wraps the TCP reader in a `BufReader` and `FramedRead` to efficiently read lines with a maximum length.
    /// 2. Uses `tokio::select!` to concurrently:
    ///    - Listen for server-to-client messages from `downstream_receiver` and write them to the TCP stream.
    ///    - Read miner requests line by line from the TCP stream, parse them as JSON, and forward to
    ///      `handle_client_to_server_request`.
    /// 3. Logs important events such as received messages, connection closures, or errors.
    ///
    /// # Returns
    /// * `Ok(())` – Connection terminated normally (client closed the connection).
    /// * `Err(Box<StratumErrors>)` – On stream reading/writing errors or if the request handling fails.
    ///
    pub async fn handle_connection(
        downstream_client: Arc<Mutex<DownstreamClient>>,
        peer_addr: SocketAddr,
        stream_reader: OwnedReadHalf,
        mut stream_writer: OwnedWriteHalf,
        downstream_receiver: &mut mpsc::Receiver<String>,
        mining_job_map: Arc<Mutex<MiningJobMap>>,
        downstream_message_sender: mpsc::Sender<String>,
        notification_sender: mpsc::Sender<NotifyCmd>,
    ) -> Result<(), Box<StratumErrors>> {
        const MAX_LINE_LENGTH: usize = 2_usize.pow(16);
        //It can be excessively inefficient to work directly with a AsyncRead instance. A BufReader performs large, infrequent reads on the underlying AsyncRead and maintains an in-memory buffer of the results.
        let reader = BufReader::new(stream_reader);
        //reading incoming stream frame by frame
        let mut framed = FramedRead::new(reader, LinesCodec::new_with_max_length(MAX_LINE_LENGTH));
        log::info!("Handling new connection from {}", peer_addr);

        loop {
            tokio::select! {
                Some(message) = downstream_receiver.recv()=>{
                    log::info!("Message recieved from the Server to be sent to the downstream node is - {:?}",message);
                    //Sending the notifications of new job to the downstream
                    let write_or_not = stream_writer.write_all(format!("{}\n",message).as_bytes()).await;
                    match write_or_not{
                        Ok(_)=>{
                            log::info!("Response has been written to the TcpStream successfully");

                        },
                        Err(error)=>{
                            log::error!("An error occurred while writing to the stream - {}",error);
                        }
                    }
                }
                line = framed.next().fuse() => {
                    match line {
                        Some(Ok(line)) => {
                            if line.is_empty() {
                                continue;
                            }
                            log::info!("Read line {:?} from {}...", line, peer_addr);
                        //Parsing the lines read from buffer to find out whether they are valid JSON request type to be server as per
                        //stratum or not .
                        match serde_json::from_str::<StandardRequest>(&line) {
                                Ok(request) => {
                         let server_request_res:Result<StratumResponses, StratumErrors> = downstream_client.lock().await.handle_client_to_server_request(serde_json::from_str(&line).unwrap(),mining_job_map.clone(),downstream_message_sender.clone(),notification_sender.clone(),peer_addr.to_string()).await;
                         match server_request_res{
                            Ok(_)=>{

                            },
                            Err(error)=>{
                                return Err(Box::new(error))
                            }
                         }
                                }
                                Err(e) => {
                                    log::error!("Failed to parse JSON from {}: {}. Line: '{}'", peer_addr, e, line);
                                }
                            }


                        }
                        Some(Err(e)) => {
                            log::error!("Error reading line from {}: {}", peer_addr, e);
                            return Err(Box::new(StratumErrors::UnableToReadStream { error: e }));
                        }
                        None => {
                            log::info!("Connection closed by client: {}", peer_addr);
                            break;

                        }
                    }
                }

            }
        }
        Ok(())
    }
}
#[allow(dead_code, unused)]
#[cfg(test)]
//Unit tests specific to stratum service
mod test {
    use std::{collections::HashMap, str::FromStr, sync::Arc, time::Duration};

    use super::*;
    use crate::stratum::{ConnectionMapping, MiningJobMap, NotifyCmd, Server, StratumServerConfig};
    use bitcoin::{
        absolute::LockTime, pow::CompactTargetExt, script::ScriptBufExt, Amount, BlockHash,
        BlockVersion, OutPoint, ScriptBuf, Sequence, TxIn, TxOut,
    };
    use futures::lock::Mutex;
    use tokio::{
        io::{AsyncBufReadExt, AsyncWriteExt, BufReader},
        net::TcpStream,
        sync::mpsc,
    };

    #[tokio::test]
    pub async fn server_start_test() {
        let connection_mapping = Arc::new(Mutex::new(ConnectionMapping::new()));
        let mining_job_map = Arc::new(Mutex::new(std::collections::HashMap::new()));
        let notify_tx = mpsc::channel::<NotifyCmd>(32).0;

        let config = StratumServerConfig {
            hostname: "127.0.0.1".to_string(),
            port: 3353,
            ..Default::default()
        };

        let mut server = Server::new(config.clone(), connection_mapping.clone());

        let server_task = tokio::spawn(async move {
            let _ = server.run_stratum_service(mining_job_map, notify_tx).await;
        });

        tokio::time::sleep(Duration::from_millis(300)).await;

        let addr = format!("{}:{}", config.hostname, config.port);
        let mut mock_connection_handles = Vec::new();
        for i in 0..3 {
            let addr_clone = addr.clone();
            mock_connection_handles.push(tokio::spawn(async move {
                let mut stream = TcpStream::connect(&addr_clone).await.unwrap();
                let msg = format!(
                    r#"{{"id":{},"method":"mining.subscribe","params":[]}}"#,
                    i + 1
                );
                stream.write_all(msg.as_bytes()).await.unwrap();
                stream.write_all(b"\n").await.unwrap();
                stream
            }));
        }

        let streams: Vec<TcpStream> = futures::future::join_all(mock_connection_handles)
            .await
            .into_iter()
            .map(|r| r.unwrap())
            .collect();

        tokio::time::sleep(Duration::from_millis(500)).await;

        let conn_map = connection_mapping.lock().await;
        assert_eq!(conn_map.downstream_channel_mapping.len(), 3);
        drop(streams);
        drop(server_task);
    }

    #[tokio::test]
    pub async fn server_subscribe_response() {
        let connection_mapping = Arc::new(Mutex::new(ConnectionMapping::new()));
        let mining_job_map = Arc::new(Mutex::new(std::collections::HashMap::new()));
        let notify_tx = mpsc::channel::<NotifyCmd>(32).0;

        let config = StratumServerConfig {
            hostname: "127.0.0.1".to_string(),
            port: 3356,
            ..Default::default()
        };

        let mut server = Server::new(config.clone(), connection_mapping.clone());

        let server_task = tokio::spawn(async move {
            let _ = server.run_stratum_service(mining_job_map, notify_tx).await;
        });

        tokio::time::sleep(Duration::from_millis(300)).await;

        let addr = format!("{}:{}", config.hostname, config.port);
        let mut stream = TcpStream::connect(&addr).await.unwrap();

        let msg = r#"{"id":1,"method":"mining.subscribe","params":[]}"#;
        stream.write_all(msg.as_bytes()).await.unwrap();
        stream.write_all(b"\n").await.unwrap();

        let mut reader = BufReader::new(stream);
        let mut response_line = String::new();
        reader.read_line(&mut response_line).await.unwrap();

        let parsed: serde_json::Value = serde_json::from_str(response_line.trim()).unwrap();
        println!("{:?}", parsed);
    }
    #[tokio::test]
    async fn test_mining_authorize_response() {
        let connection_mapping = Arc::new(Mutex::new(ConnectionMapping::new()));
        let mining_job_map = Arc::new(Mutex::new(std::collections::HashMap::new()));
        let notify_tx = mpsc::channel::<NotifyCmd>(32).0;

        let config = StratumServerConfig {
            hostname: "127.0.0.1".to_string(),
            port: 3357,
            ..Default::default()
        };

        let port = config.port;
        let mut server = Server::new(config, connection_mapping);
        tokio::spawn(async move {
            let _ = server.run_stratum_service(mining_job_map, notify_tx).await;
        });

        tokio::time::sleep(Duration::from_millis(300)).await;

        let addr = format!("127.0.0.1:{}", port);
        let mut stream = TcpStream::connect(&addr).await.unwrap();

        let request = r#"{"id":2,"method":"mining.authorize","params":["satoshi","braidpool"]}"#;
        stream.write_all(request.as_bytes()).await.unwrap();
        stream.write_all(b"\n").await.unwrap();
        let mut reader = BufReader::new(stream);

        let mut line = String::new();
        reader.read_line(&mut line).await.unwrap();
        let response: serde_json::Value = serde_json::from_str(line.trim()).unwrap();

        assert_eq!(response["id"], 2);
        assert!(response["result"].is_boolean());
        assert_eq!(response["result"], true);
    }
    #[tokio::test]
    async fn test_mining_set_difficulty_response() {
        let connection_mapping = Arc::new(Mutex::new(ConnectionMapping::new()));
        let mining_job_map = Arc::new(Mutex::new(std::collections::HashMap::new()));
        let notify_tx = mpsc::channel::<NotifyCmd>(32).0;

        let config = StratumServerConfig {
            hostname: "127.0.0.1".to_string(),
            port: 3358,
            ..Default::default()
        };
        let port = config.port;
        let mut server = Server::new(config, connection_mapping);
        tokio::spawn(async move {
            let _ = server.run_stratum_service(mining_job_map, notify_tx).await;
        });
        tokio::time::sleep(Duration::from_millis(300)).await;
        let addr = format!("127.0.0.1:{}", port);
        let mut stream = TcpStream::connect(&addr).await.unwrap();
        let request = r#"{"id":3,"method":"mining.suggest_difficulty","params":[1000]}"#;
        stream.write_all(request.as_bytes()).await.unwrap();
        stream.write_all(b"\n").await.unwrap();
        let mut reader = BufReader::new(stream);
        let mut line = String::new();
        reader.read_line(&mut line).await.unwrap();
        let response: serde_json::Value = serde_json::from_str(line.trim()).unwrap();
        assert_eq!(response["method"], "mining.set_difficulty");
    }
    #[tokio::test]
    async fn test_invalid_json() {
        let connection_mapping = Arc::new(Mutex::new(ConnectionMapping::new()));
        let mining_job_map: Arc<Mutex<HashMap<String, Arc<Mutex<MiningJobMap>>>>> =
            Arc::new(Mutex::new(HashMap::new()));
        let (notify_tx, _notify_rx) = mpsc::channel::<NotifyCmd>(32);

        let config = StratumServerConfig {
            hostname: "127.0.0.1".to_string(),
            port: 5050,
            ..Default::default()
        };

        let mut server = Server::new(config, connection_mapping.clone());
        let mining_job_map_clone = mining_job_map.clone();
        let notify_tx_clone = notify_tx.clone();
        tokio::spawn(async move {
            server
                .run_stratum_service(mining_job_map_clone, notify_tx_clone)
                .await
                .unwrap();
        });

        tokio::time::sleep(std::time::Duration::from_millis(200)).await;

        let mut stream = TcpStream::connect("127.0.0.1:5050").await.unwrap();

        stream
            .write_all(b"{\"method\":\"mining.subscribe\", \"params\": [\"test\", 1]\n")
            .await
            .unwrap();
        stream.flush().await.unwrap();

        stream.write_all(b"not a json at all\n").await.unwrap();
        stream.flush().await.unwrap();

        tokio::time::sleep(std::time::Duration::from_millis(200)).await;

        let valid_msg = r#"{"id": 1, "method": "mining.subscribe", "params": []}"#;
        stream
            .write_all(format!("{}\n", valid_msg).as_bytes())
            .await
            .unwrap();
        stream.flush().await.unwrap();

        let mut reader = BufReader::new(stream);
        let mut line = String::new();
        let bytes_read = reader.read_line(&mut line).await.unwrap();
        let response: serde_json::Value = serde_json::from_str(line.trim()).unwrap();
        assert_eq!(response["id"], 1);
    }

    //TODO: this test is currently conditional wrt to master branch for our forked rust-bitcoin hence commented out

    #[tokio::test]
    async fn submit_work_no_version_rolling() {
        /*
        Test block taken - 00000020e6ebb395a1e2ba60f17650d790309e21af08062229ad955376ac574300000000e8de27818e402a0d5e6028f363be4b47d809ad348e6bc88ac2f9c2bedf0409e9337edf68ffff001d7aeb8b0601020000000001010000000000000000000000000000000000000000000000000000000000000000ffffffff1602611e089495ac0803000000094272616964706f6f6cffffffff0300f2052a01000000160014e470d0179325db88b55771f6c0a5139dd81d73180000000000000000266a24aa21a9ede2f61c3f71d1defd3fa999dfa36953755c690689799962b48bebd836974e8cf900000000000000002a6a286272616964706f6f6c5f626561645f6d657461646174615f686173685f33326201020304050607080120000000000000000000000000000000000000000000000000000000000000000000000000

         */
        let test_merkel_bytes: [u8; 32] = [0u8; 32];
        let mut test_witness = Witness::new();
        test_witness.push(vec![0u8; 32]);
        //Little more doubt in construction of initial coinbase only and in merkel which can be due to coinbase only
        //There is a case in prevblockhash too but it can be discussed afterwards
        //Cleaning up connection channels from connection mapping as well as from global map arc of stratum server
        let test_coinbase_transaction: Transaction = Transaction {
            version: bitcoin::TransactionVersion::TWO,
            input: vec![TxIn {
                previous_output: OutPoint {
                    txid: Txid::from_str(
                        "0000000000000000000000000000000000000000000000000000000000000000",
                    )
                    .unwrap(),
                    vout: OutPoint::COINBASE_PREVOUT.vout,
                },
                script_sig: ScriptBuf::from_hex(
                    "02611e080101010101010101094272616964706f6f6c",
                )
                .unwrap(),
                sequence: Sequence::MAX,
                witness: test_witness.clone(),
            }],
            output: vec![
                TxOut {
                    value: Amount::FIFTY_BTC,
                    script_pubkey: ScriptBuf::from_hex("0014e470d0179325db88b55771f6c0a5139dd81d7318")
                        .unwrap(),
                },
                TxOut {
                    value: Amount::from_sat(0).unwrap(),
                    script_pubkey: ScriptBuf::from_hex("6a24aa21a9ede2f61c3f71d1defd3fa999dfa36953755c690689799962b48bebd836974e8cf9")
                        .unwrap(),
                },
                TxOut {
                    value: Amount::from_sat(0).unwrap(),
                    script_pubkey: ScriptBuf::from_hex(
                        "6a286272616964706f6f6c5f626561645f6d657461646174615f686173685f3332620102030405060708",
                    )
                    .unwrap(),
                },
            ],
            lock_time: LockTime::ZERO,
        };
        let test_template_header = bitcoin::block::Header {
            bits: bitcoin::pow::CompactTarget::from_unprefixed_hex("1d00ffff").unwrap(),
            nonce: 0,
            version: BlockVersion::from_consensus(536870912),
            time: BlockTime::from_u32(1759477299),
            prev_blockhash: BlockHash::from_str(
                "000000004357ac765395ad29220608af219e3090d75076f160bae2a195b3ebe6",
            )
            .unwrap(),
            merkle_root: TxMerkleNode::from_byte_array(test_merkel_bytes),
        };
        let mut test_template = BlockTemplate {
            version: test_template_header.version,
            previousblockhash: test_template_header.prev_blockhash,
            transactions: vec![test_coinbase_transaction],
            curtime: test_template_header.time,
            bits: test_template_header.bits,
            ..Default::default()
        };
        let mut constructed_test_notification =
            Notifier::construct_job_notification(false, test_template.clone(), 1, vec![])
                .await
                .unwrap();
        println!("{:?}", constructed_test_notification);
        let constructed_test_notification_ref = constructed_test_notification.clone();
        let mut mock_downstream_handler = DownstreamClient::default();
        let mock_mining_job_map: Arc<Mutex<MiningJobMap>> =
            Arc::new(Mutex::new(MiningJobMap::new()));
        test_template.transactions.remove(0);
        let job_details = JobDetails {
            blocktemplate: test_template,
            coinbase1: constructed_test_notification_ref.clone().coinbase1.clone(),
            coinbase2: constructed_test_notification_ref.clone().coinbase2.clone(),
            coinbase_merkel_path: vec![],
            coinbase_witness_commitment: Some(test_witness),
        };
        mock_mining_job_map
            .lock()
            .await
            .insert_mining_job(job_details.clone())
            .await;
        let test_submit_request_params =
            json!(["bitaxe", "1", "03000000", "68df7e33", "068beb7a",]);
        let configure_test_request = json!([
            [
                "version-rolling"
            ],
            {
                "version-rolling.mask": "ffffffff"
            }
        ]);
        let test_extranonce_1 = hex::decode("9495ac08").unwrap();
        mock_downstream_handler.extranonce1 = test_extranonce_1;
        let configure_response = mock_downstream_handler
            .handle_configure(&configure_test_request, 1)
            .await;
        let submit_response: StratumResponses = mock_downstream_handler
            .handle_submit(&test_submit_request_params, mock_mining_job_map.clone(), 2)
            .await
            .unwrap();
        match submit_response {
            StratumResponses::StandardResponse { std_response } => {
                let resp = std_response.result.unwrap();
                let json_response = resp.as_bool().unwrap();
                assert_eq!(json_response, true);
            }
            _ => {
                println!("Invalid response received");
            }
        }
    }
    #[test]
    fn prev_hash_test() {
        let prev_test_hash = "00000000cbdd48c69c45ffd07dc26fc3668bb70870374354535061f8f5304c7c";
        let reversed_hash = reverse_four_byte_chunks(prev_test_hash).unwrap();

        assert_eq!(
            reversed_hash,
            "f5304c7c535061f870374354668bb7087dc26fc39c45ffd0cbdd48c600000000".to_string()
        );
    }
    #[test]
    fn test_merkel_root_construction() {
        let coinbase_string_non_segwit = "02000000010000000000000000000000000000000000000000000000000000000000000000ffffffff170305190408ac53db1b00000000094272616964706f6f6cffffffff03c81d039500000000160014af0ce4a33e61762bde14de428440a9def7acc9310000000000000000266a24aa21a9edac3e72f41e3e7cda29fa3e372e7209108db9c2b2bff9e7b51fdffb10b89a9e4300000000000000002a6a286272616964706f6f6c5f626561645f6d657461646174615f686173685f333262010203040506070800000000";
        let coinbase_bytes = hex::decode(coinbase_string_non_segwit).unwrap();
        let mut cursor = Cursor::new(coinbase_bytes);
        let coinbase_tx = Transaction::consensus_decode(&mut cursor).unwrap();
        let coinbase_wtxid = coinbase_tx.compute_wtxid();
        let coinbase_txid = coinbase_tx.compute_txid();
        assert_eq!(coinbase_txid.to_string(), coinbase_wtxid.to_string());
        let test_merkel_branches = [
            "0ce0d53011438c88cdff30f6312ca67d87bf14fb39e449a5cf90cd369d750e21",
            "562d5094b1362ac66b126a910908eea2a17b06891483ee90447914dcad65c96b",
            "d485ae53320318f499c91e3b8899c004d10ba358aa143ace70aab9f4448aac0e",
            "37aabcd6778b0a07f06c7d9f5f12ca156b679bdf69f1c6327a06d30c0002b49d",
            "408040846f74ad0a82e58a17431b8fde5f62e5e913f34ffe21e29b907eda7e0f",
        ];
        let mut merkel_branches_serialized: Vec<Vec<u8>> = Vec::new();
        for merkle_branch_str in test_merkel_branches {
            let mut merkel_branch_bytes: [u8; 32] = [0u8; 32];
            hex::decode_to_slice(merkle_branch_str, &mut merkel_branch_bytes).unwrap();
            merkel_branches_serialized.push(Vec::from(merkel_branch_bytes));
        }
        println!("Merkel branches bytes - {:?}", merkel_branches_serialized);
        let merkel_root_bytes =
            calculate_merkle_root(coinbase_txid, &merkel_branches_serialized.as_slice());
        let mr = TxMerkleNode::from_byte_array(merkel_root_bytes);
        println!("Merkel root - {:?}", mr.to_string());
        assert_eq!(
            mr.to_string(),
            "690699e45d09d84d81cb58a4f8ba734e7fc90856d8b24524797f9a54ff57b1a1".to_string()
        );
    }
}
