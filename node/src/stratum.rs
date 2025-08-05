#![allow(unused)]
use crate::error::StratumErrors;
use bitcoin::block::HeaderExt;
use bitcoin::blockdata::block::Block;
use bitcoin::consensus::serialize;
use bitcoin::io::Cursor;
use bitcoin::merkle_tree::MerkleNode;
use bitcoin::pow::CompactTargetExt;
use bitcoin::{
    absolute::{Decodable, Encodable},
    consensus::deserialize,
    io::{self, BufRead, Write},
    Transaction,
};
use bitcoin::{merkle_tree, BlockHeader, BlockTime, TxMerkleNode, Txid};
use bitcoincore_rpc::bitcoin::block::Header;
use futures::channel;
use futures::{lock::Mutex, FutureExt};
use rand::RngCore;
use serde::{Deserialize, Serialize};
use serde_json::{json, Value};
use std::str::FromStr;
use std::{borrow::Cow, collections::HashMap, net::SocketAddr, sync::Arc};
use tokio::{
    io::{AsyncWriteExt, BufReader},
    net::{
        tcp::{self, OwnedReadHalf, OwnedWriteHalf},
        TcpListener, TcpStream,
    },
    sync::mpsc,
};
use tokio_stream::StreamExt;
use tokio_util::codec::{FramedRead, LinesCodec};

//4 byte extranonce prefix
pub const EXTRANONCE1_SIZE: usize = 4;
//8 byte extranonce suffix just for testing it is set to 4 bytes reset accordingly
pub const EXTRANONCE2_SIZE: usize = 4;
//Total extranonce length to be kept as testing = 8 bytes
pub const EXTRANONCE_SEPARATOR: [u8; EXTRANONCE1_SIZE + EXTRANONCE2_SIZE] =
    [1u8; EXTRANONCE1_SIZE + EXTRANONCE2_SIZE];
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

/// Struct representing the getblocktemplate response from Bitcoin Core
/// as provided under BIPS-0022 - https://github.com/bitcoin/bips/blob/master/bip-0022.mediawiki
/// https://github.com/bitcoin/bitcoin/blob/master/src/rpc/mining.cpp#L610
#[derive(Debug, Deserialize, Serialize, Clone)]
pub struct BlockTemplate {
    pub version: i32,
    pub rules: Option<Vec<String>>,
    pub vbavailable: Option<Vec<(String, i32)>>,
    pub vbrequired: Option<u32>,
    pub previousblockhash: String,
    pub transactions: Vec<Transaction>,
    pub coinbaseaux: Option<Vec<(String, String)>>,
    pub coinbasevalue: Option<u64>,
    pub longpollid: Option<String>,
    pub target: String,
    pub mintime: Option<u32>,
    pub mutable: Option<Vec<String>>,
    pub noncerange: Option<String>,
    pub sigoplimit: Option<u32>,
    pub sizelimit: Option<u32>,
    pub weightlimit: Option<u32>,
    pub curtime: u32,
    pub bits: String,
    pub height: u32,
    pub default_witness_commitment: Option<String>,
}
impl Encodable for BlockTemplate {
    fn consensus_encode<W: Write + ?Sized>(&self, writer: &mut W) -> Result<usize, io::Error> {
        let mut len = 0;

        len += self.version.consensus_encode(writer).unwrap();

        if let Some(rules) = &self.rules {
            len += (rules.len() as u64).consensus_encode(writer).unwrap();
            for rule in rules {
                len += rule.consensus_encode(writer).unwrap();
            }
        } else {
            len += 0u64.consensus_encode(writer).unwrap();
        }

        if let Some(version_bits_available) = &self.vbavailable {
            len += (version_bits_available.len() as u64)
                .consensus_encode(writer)
                .unwrap();
            for (key, value) in version_bits_available {
                len += key.consensus_encode(writer).unwrap();
                len += value.consensus_encode(writer).unwrap();
            }
        } else {
            len += 0u64.consensus_encode(writer).unwrap();
        }

        if let Some(version_bits_required) = self.vbrequired {
            len += version_bits_required.consensus_encode(writer).unwrap();
        }

        len += self.previousblockhash.consensus_encode(writer).unwrap();

        len += (self.transactions.len() as u64)
            .consensus_encode(writer)
            .unwrap();
        for transaction in &self.transactions {
            len += transaction.consensus_encode(writer).unwrap();
        }

        if let Some(coinbase_auxiliary) = &self.coinbaseaux {
            len += (coinbase_auxiliary.len() as u64)
                .consensus_encode(writer)
                .unwrap();
            for (key, value) in coinbase_auxiliary {
                len += key.consensus_encode(writer).unwrap();
                len += value.consensus_encode(writer).unwrap();
            }
        } else {
            len += 0u64.consensus_encode(writer).unwrap();
        }

        if let Some(coinbase_value) = self.coinbasevalue {
            len += coinbase_value.consensus_encode(writer).unwrap();
        }

        if let Some(long_poll_id) = &self.longpollid {
            len += long_poll_id.consensus_encode(writer).unwrap();
        }

        len += self.target.consensus_encode(writer).unwrap();

        if let Some(minimum_time) = self.mintime {
            len += minimum_time.consensus_encode(writer).unwrap();
        }

        if let Some(mutable_fields) = &self.mutable {
            len += (mutable_fields.len() as u64)
                .consensus_encode(writer)
                .unwrap();
            for mutable_entry in mutable_fields {
                len += mutable_entry.consensus_encode(writer).unwrap();
            }
        } else {
            len += 0u64.consensus_encode(writer).unwrap();
        }

        if let Some(nonce_range) = &self.noncerange {
            len += nonce_range.consensus_encode(writer).unwrap();
        }

        if let Some(signature_operation_limit) = self.sigoplimit {
            len += signature_operation_limit.consensus_encode(writer).unwrap();
        }

        if let Some(size_limit) = self.sizelimit {
            len += size_limit.consensus_encode(writer).unwrap();
        }

        if let Some(weight_limit) = self.weightlimit {
            len += weight_limit.consensus_encode(writer).unwrap();
        }

        len += self.curtime.consensus_encode(writer).unwrap();
        len += self.bits.consensus_encode(writer).unwrap();
        len += self.height.consensus_encode(writer).unwrap();

        if self.default_witness_commitment.is_none() == false {
            for witness_commitmment in self.default_witness_commitment.clone() {
                len += witness_commitmment.consensus_encode(writer)?;
            }
        }
        log::info!("LENGTH DURING SERIALIZATION - {:?}", len);
        Ok(len)
    }
}
impl Default for BlockTemplate {
    fn default() -> Self {
        Self {
            version: 0,
            rules: None,
            vbavailable: None,
            vbrequired: None,
            previousblockhash: String::new(),
            transactions: Vec::new(),
            coinbaseaux: None,
            coinbasevalue: None,
            longpollid: None,
            target: String::new(),
            mintime: None,
            mutable: None,
            noncerange: None,
            sigoplimit: None,
            sizelimit: None,
            weightlimit: None,
            curtime: 0,
            bits: String::new(),
            height: 0,
            default_witness_commitment: None,
        }
    }
}
#[derive(Debug, Clone)]
pub struct StratumServerConfig {
    pub hostname: String,
    pub port: u16,
    pub start_difficulty: u64,
    pub minimum_difficulty: u64,
    pub maximum_difficulty: Option<u64>,
    pub solo_address: Option<String>,
}

impl Default for StratumServerConfig {
    fn default() -> Self {
        Self {
            hostname: String::from("0.0.0.0"),
            port: 3333,
            start_difficulty: 1,
            minimum_difficulty: 1,
            maximum_difficulty: None,
            solo_address: None,
        }
    }
}
#[derive(Clone, Serialize, Deserialize, Debug, PartialEq, Eq)]
pub struct StandardRequest {
    pub id: u64,
    pub method: String,
    pub params: serde_json::Value,
}
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum StratumResponses {
    StandardResponse {
        std_response: StandardResponse,
    },
    SuggestDifficultyResponse {
        suggest_difficulty_resp: SuggestDifficultyResponse,
    },
}
/// Response represents a Stratum response message from the server to the client
/// We use Value in result to allow for different types of responses.
/// TODO: Consider using various Response types to avoing using Value (which will result in memory allocations)
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
/// Target is a 256-bit unsigned integer in little-endian
/// instead of using `BigUint` i have taken into account u128 for respective MSB and LSB
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Target {
    lsb: u128,
    msb: u128,
}
#[derive(Debug, Clone)]
pub struct DownstreamClient {
    ///Authorized or not
    pub authorized: bool,
    ///Downstream miner IP
    pub downstream_ip: String,
    /// Did the mine subscribe already?
    pub subscribed: bool,
    /// The unique identifier assigned to this downstream connection/channel.
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
    // Current target
    pub target: Target,
}
impl DownstreamClient {
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
            "mining.suggest_difficulty" => {
                self.suggest_difficulty(&req_params, client_request_id)
                    .await
            }
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
                if self.authorized == true && self.subscribed == true {
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
                            log::error!("An error occurred while requesting latest template by a newly authorized downstream node");
                        }
                    }
                }
                // if let Err(e) = stream_writer
                //     .write_all(format!("{}\n", response_json_string).as_bytes())
                //     .await
                // {
                //     log::error!("Error while writing to TCP stream");
                //     return Err(StratumErrors::ResponseWriteError { error: e });
                // } else {
                //     log::info!("Response has been written to the TcpStream successfully");
                // }
                Ok(stratum_response)
            }
            Err(error) => {
                log::error!("{}", error);
                Err(error)
            }
        }
    }
    // (46733) stratum_api: tx: {"id": 5, "method": "mining.submit", "params": ["bc1qnp980s5fpp8l94p5cvttmtdqy8rvrq74qly2yrfmzkdsntqzlc5qkc4rkq.bitaxe", "2", "09000000", "6891e02b", "91e70222", "034ea000"]}
    pub async fn handle_submit(
        &mut self,
        submit_work_params: &Value,
        mut mining_job_map: Arc<Mutex<MiningJobMap>>,
        client_request_id: u64,
    ) -> Result<StratumResponses, StratumErrors> {
        let param_array = submit_work_params.as_array().unwrap();
        if param_array.len() < 5 {
            return Err(StratumErrors::InvalidMethodParams {
                method: "mining.submit".to_string(),
            });
        }
        let worker_name_res: Result<&str, StratumErrors> = match param_array.get(0) {
            Some(worker_name) => Ok(worker_name.as_str().unwrap()),
            None => Err(StratumErrors::InvalidMethodParams {
                method: "mining.submit".to_string(),
            }),
        };
        let worker_name = match worker_name_res {
            Ok(name) => name,
            Err(error) => return Err(error),
        };
        let job_id_str: &Value = param_array.get(1).unwrap();
        let job_id = u64::from_str_radix(job_id_str.as_str().unwrap(), 16).unwrap();
        let extranonce2: &str = match param_array.get(2).and_then(|v| v.as_str()) {
            Some(extra) => extra,
            None => {
                return Err(StratumErrors::InvalidMethodParams {
                    method: "mining.submit".to_string(),
                })
            }
        };

        let ntime: &str = match param_array.get(3).and_then(|v| v.as_str()) {
            Some(nt) => nt,
            None => {
                return Err(StratumErrors::InvalidMethodParams {
                    method: "mining.submit".to_string(),
                })
            }
        };

        let nonce: &str = match param_array.get(4).and_then(|v| v.as_str()) {
            Some(n) => n,
            None => {
                return Err(StratumErrors::InvalidMethodParams {
                    method: "mining.submit".to_string(),
                })
            }
        };
        //acquring lock on the mining map and fetching the submitted job from the memory
        let mut job_mapping = mining_job_map.lock().await;
        let job_r = job_mapping.get_mining_job(job_id).await;
        let submitted_job = match job_r {
            Ok(job) => job,
            Err(error) => {
                return Err(StratumErrors::MiningJobNotFound { job_id: job_id });
            }
        };
        //building the coinbase and then eventually the block and testing for the validation against the
        //mainnet difficulty or the weakshare local difficulty
        let extranonce_1_hex = hex::encode(self.extranonce1.clone());
        let coinbase_tx_hex = format!(
            "{}{}{}{}",
            submitted_job.coinbase1,
            extranonce_1_hex,
            extranonce2.to_ascii_lowercase(),
            submitted_job.coinbase2
        );
        let coinbase_bytes = hex::decode(coinbase_tx_hex).unwrap();
        let mut coinbase_cursor = Cursor::new(coinbase_bytes);
        let coinbase_tx: Transaction =
            bitcoin::Transaction::consensus_decode(&mut coinbase_cursor).unwrap();

        //computing merkel new merkel path due to updated coinbase transaction
        let txs = submitted_job.blocktemplate.transactions.clone();
        let mut txids: Vec<Txid> = vec![coinbase_tx.compute_txid()];
        for tx in txs.iter() {
            txids.push(tx.compute_txid());
        }
        let merkle_root: TxMerkleNode = TxMerkleNode::calculate_root(txids.into_iter()).unwrap();

        //applying version mask received during mining.configure or not TODO
        let version = submitted_job.blocktemplate.version.clone();
        //computing the block header
        let header = BlockHeader {
            version: bitcoin::blockdata::block::Version::from_consensus(version),
            prev_blockhash: bitcoin::BlockHash::from_str(
                &submitted_job.blocktemplate.previousblockhash,
            )
            .unwrap(),
            merkle_root: merkle_root,
            time: BlockTime::from_u32(u32::from_str_radix(ntime, 16).unwrap()),
            bits: bitcoin::pow::CompactTarget::from_unprefixed_hex(
                &submitted_job.blocktemplate.bits,
            )
            .unwrap(),
            nonce: u32::from_str_radix(nonce, 16).unwrap(),
        };
        let compact_target =
            bitcoin::CompactTarget::from_unprefixed_hex(&submitted_job.blocktemplate.bits).unwrap();
        let target = bitcoin::Target::from_compact(compact_target);
        //checking with PoW of the target whether the block sent by downstream is below that or not
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
    pub async fn suggest_difficulty(
        &mut self,
        suggest_difficulty_params: &Value,
        client_request_id: u64,
    ) -> Result<StratumResponses, StratumErrors> {
        if let Some(difficulty) = suggest_difficulty_params.get(0) {
            log::info!(
                "Handling suggested difficulty - {}",
                suggest_difficulty_params
            );
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
    pub async fn handle_authorize(
        &mut self,
        authorize_request_params: &Value,
        client_request_id: u64,
    ) -> Result<StratumResponses, StratumErrors> {
        log::info!(
            "Authorization is taking place -- {:?}",
            authorize_request_params
        );
        let param_array = authorize_request_params.as_array().unwrap();
        let username_res: Result<&str, StratumErrors> = match param_array.get(0) {
            Some(user) => Ok(user.as_str().unwrap()),
            None => {
                return Err(StratumErrors::InvalidMethodParams {
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
            None => {
                return Err(StratumErrors::InvalidMethodParams {
                    method: "mining.authorize".to_string(),
                });
            }
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
        let params = config_req_params
            .as_array()
            .ok_or("Expected params to be an array")
            .unwrap();

        if params.len() != 2 {
            return Err(StratumErrors::InvalidMethodParams {
                method: "mining.configure".to_string(),
            });
        }

        let features = params[0]
            .as_array()
            .ok_or("Expected first param to be an array of feature names")
            .unwrap();

        let feature_names: Vec<String> = features
            .iter()
            .map(|f| f.as_str().map(|s| s.to_string()))
            .collect::<Option<Vec<String>>>()
            .ok_or("Invalid feature name in features array")
            .unwrap();
        log::info!("{:?}", feature_names);
        let config_map = params[1]
            .as_object()
            .ok_or("Expected second param to be an object with feature configurations")
            .unwrap();
        log::info!("{:?}", config_map);

        let minimum_difficulty = config_map.get("minimum-difficulty.value").or(None);
        let version_rolling_mask = config_map.get("version-rolling.mask").or(None);
        let version_rolling_min_bit_count =
            config_map.get("version-rolling.min-bit-count").or(None);
        if version_rolling_mask.is_none() == false {
            let mut mask_bytes: [u8; 4] = [0u8; 4];
            let version_rolling_mask_str = version_rolling_mask.unwrap().as_str().unwrap();
            hex::decode_to_slice(version_rolling_mask_str, &mut mask_bytes);

            let final_rollable_version_bits = u32::from_be_bytes(mask_bytes) & 0x1FFFE000;
            // `0x1FFFE000` is a reasonable default as it allows all 16 version bits to be used
            let hex_str = u32::to_string(&final_rollable_version_bits);
            self.version_rolling_mask = Some(hex_str);
        }
        if version_rolling_min_bit_count.is_none() == false {
            let mut mask_bytes: [u8; 4] = [0u8; 4];
            let version_rolling_min_bit_count_str =
                version_rolling_min_bit_count.unwrap().as_str().unwrap();
            hex::decode_to_slice(version_rolling_min_bit_count_str, &mut mask_bytes);
            self.version_rolling_min_bit = Some(u32::from_be_bytes(mask_bytes));
        }

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
    ///The optional second parameter specifies a mining.notify subscription id the client wishes to resume working with (possibly due to a dropped connection). If provided, a server MAY (at its option) issue the connection the same extranonce1. Note that the extranonce1 may be the same (allowing a resumed connection) even if the subscription id is changed!
    /// The result contains three items:

    /// Subscriptions. - An array of 2-item tuples, each with a subscription type and id.
    /// ExtraNonce1. - Hex-encoded, per-connection unique string which will be used for creating generation transactions later.
    /// ExtraNonce2_size. - The number of bytes that the miner users for its ExtraNonce2 counter.
    pub async fn handle_subscribe(
        &mut self,
        subscribe_req_params: &Value,
        client_request_id: u64,
    ) -> Result<StratumResponses, StratumErrors> {
        log::info!("Subscribing is taking place -- {:?}", subscribe_req_params);
        //FIXME dummy testing subscription IDs must be unique though
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

    // Server response is result: true for accepted, false for rejected (or you may get an error with more details).
    // pub async fn handle_submit(
    //     submit_job_request: &Value,
    //     req_id: u64,
    // ) -> Result<Response, StratumErrors> {
    // }
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
            //generating a random u32 client connection id
            connection_id: rand::thread_rng().next_u32(),
            extranonce1: Vec::from(extranonce1_bytes),
            version_rolling_mask: None,
            version_rolling_min_bit: None,
            extranonce2_len: EXTRANONCE2_SIZE,
            target: Target { lsb: 1, msb: 2 },
        }
    }
}

#[derive(Debug)]
pub struct Server {
    stratum_config: StratumServerConfig,
    downstream_connection_mapping: Arc<Mutex<ConnectionMapping>>, // downstream_miner: Arc<Mutex<DownstreamClient>>,
                                                                  // pub downstream_sender: mpsc::Sender<String>,
                                                                  // pub downstream_receiver: mpsc::Receiver<String>,
}
pub enum NotifyCmd {
    SendToAll {
        template: BlockTemplate,
        merkel_branch_coinbase: Vec<Vec<u8>>,
    },
    SendLatestTemplateToNewDownstream {
        new_downstream_addr: String,
    },
}
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
}
#[derive(Debug, Clone)]
pub struct JobDetails {
    pub blocktemplate: BlockTemplate,
    pub coinbase1: String,
    pub coinbase2: String,
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
    ///Inserting a suitable mining job which has been passed to the downstream being constructed from a suitable block template
    pub async fn insert_mining_job(&mut self, job_details: JobDetails) {
        log::info!(
            "Inserting new mining job with job_id: {}",
            self.latest_job_id + 1
        );
        self.mining_jobs.insert(self.latest_job_id + 1, job_details);
    }
    ///Getting a mining job from the existing jobs upto a given timestamp t used by the downstream node for mining
    /// also served as the response for mining.getjob method from client2server in stratum
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
        self.latest_job_id = self.latest_job_id + 1;
        log::info!("Generated next job_id: {}", self.latest_job_id);
        self.latest_job_id
    }
}
pub struct Notifier {
    notification_receiver: mpsc::Receiver<NotifyCmd>,
    pub job_map_arc: Arc<Mutex<HashMap<String, Arc<Mutex<MiningJobMap>>>>>,
}
fn to_little_endian(hex_str: &str) -> String {
    hex_str
        .as_bytes()
        .chunks(2)
        .map(|chunk| std::str::from_utf8(chunk).unwrap())
        .rev()
        .collect::<Vec<&str>>()
        .join("")
}
impl Notifier {
    pub fn new(
        notification_rx: mpsc::Receiver<NotifyCmd>,
        job_map_arc: Arc<Mutex<HashMap<String, Arc<Mutex<MiningJobMap>>>>>,
    ) -> Self {
        Self {
            notification_receiver: notification_rx,
            job_map_arc: job_map_arc,
        }
    }
    //Constructing the mining.notify template following the corrsponding attributes to be sent as a job to the downstream miner for
    //mining to take place .
    /*
    Job ID. This is included when miners submit a results so work can be matched with proper transactions.
    Hash of previous block. Used to build the header.
    Generation transaction (part 1). The miner inserts ExtraNonce1 and ExtraNonce2 after this section of the transaction data.
    Generation transaction (part 2). The miner appends this after the first part of the transaction data and the two ExtraNonce values.
    List of merkle branches. The generation transaction is hashed against the merkle branches to build the final merkle root.
    Bitcoin block version. Used in the block header.
    nBits. The encoded network difficulty. Used in the block header.
    nTime. The current time. nTime rolling should be supported, but should not increase faster than actual time.
    Clean Jobs. If true, miners should abort their current work and immediately use the new job, even if it degrades hashrate in the short term. If false, they can still use the current job, but should move to the new one as soon as possible without impacting hashrate.
     */
    pub async fn construct_job_notification(
        clean_job: bool,
        notified_template: BlockTemplate,
        new_job_id: u64,
        merkel_coinbase_branch: Vec<Vec<u8>>,
    ) -> Result<JobNotification, StratumErrors> {
        log::info!(
            "Constructing JobNotification for job_id: {} with clean_job: {}",
            new_job_id,
            clean_job
        );

        //PLACEHOLDERS FOR VALID COINBASE ALONG WITH VALID MERKEL BRANCHES TO BE PROVIDED IN JOB
        //WILL HAVE TO BE REPLACED WITH construct_coinbase and construct_merkel_branches functions respectively .
        //Splitting the coinbase according to the `coinbase_prefix` and `coinbase_suffix` for
        //providing the valid bits to be rolled as per the `extranonce` value by the downstream and then appended
        //which is retreived during the `mining.submit` as client2server call .
        let coinbase_transaction = notified_template.transactions.get(0).unwrap();
        let deserialized_coinbase = serialize::<Transaction>(coinbase_transaction);
        log::info!(
            "Deserialized coinbase length is - {:?} \n and the coinbase tx is - {:?}",
            deserialized_coinbase.len(),
            coinbase_transaction
        );
        let separator_pos = match deserialized_coinbase
            .as_slice()
            .windows(EXTRANONCE1_SIZE + EXTRANONCE2_SIZE)
            .position(|window| window == EXTRANONCE_SEPARATOR)
        {
            Some(pos) => pos,
            None => return Err(StratumErrors::InvalidCoinbase),
        };

        //PLACEHOLDERS FOR VALID COINBASE ALONG WITH VALID MERKEL BRANCHES TO BE PROVIDED IN JOB
        //WILL HAVE TO BE REPLACED WITH construct_coinbase and construct_merkel_branches functions respectively .
        let coinbase_1 = hex::encode(&deserialized_coinbase[..separator_pos]);
        let coinbase_2 = hex::encode(
            &deserialized_coinbase[separator_pos + (EXTRANONCE1_SIZE + EXTRANONCE2_SIZE)..],
        );
        log::info!("Coinbase splitted with coinbase_prefix and coinbase suffix respectively as -- {:?} {:?}",coinbase_1,coinbase_2);
        let mut merkel_branches: Vec<String> = Vec::new();
        let mut txids_hashes: Vec<Txid> = vec![];
        for tx in notified_template.transactions {
            txids_hashes.push(tx.compute_txid());
        }
        if merkel_coinbase_branch.len() == 0 {
            log::info!("Empty branch hence previous template was being used and hence saving has to be done !");
        } else {
            for sibling_node in merkel_coinbase_branch.iter() {
                let sibling_hex = hex::encode(sibling_node);
                merkel_branches.push(sibling_hex);
            }
        }
        log::info!(
            "Merkel branches for the given template's coinbase are respectively - {:?}",
            merkel_branches
        );
        //stratum accepts the prev block hash to be in little endian instead of big endian
        //therefore byte by byte reversal is required here
        let mut prev_block_hash = notified_template.previousblockhash.as_str();
        let prev_block_hash_little_endian = to_little_endian(prev_block_hash);
        log::info!(
            "Converting the prev block hash to little endian done -- {:?}",
            prev_block_hash_little_endian
        );
        let bitcoin_block_version = notified_template.version;
        let bits = notified_template.bits;
        let time = notified_template.curtime;
        Ok(JobNotification {
            job_id: new_job_id.to_string(),
            prevhash: prev_block_hash_little_endian,
            coinbase1: coinbase_1,
            coinbase2: coinbase_2,
            merkle_branches: merkel_branches,
            //converting the i32 version to hex string
            version: hex::encode(bitcoin_block_version.to_be_bytes()),
            //String is acceptable
            nbits: bits,
            //ntime is to be hex encoded
            ntime: hex::encode(time.to_be_bytes()),
            clean_jobs: clean_job,
        })
    }
    ///Will run a notifier that will serve the purpose of mining.notify to provide the downstream nodes with valid jobs on the basis
    /// of the latest block template recieved/present via the template_receiver
    pub async fn run_notifier(
        &mut self,
        downstream_connection_map: Arc<Mutex<ConnectionMapping>>,
        latest_template_arc: &mut Arc<Mutex<BlockTemplate>>,
        latest_template_merkel_branch_arc: &mut Arc<Mutex<Vec<Vec<u8>>>>,
    ) -> Result<(), StratumErrors> {
        log::info!("Notifier task has  started");
        while let Some(notification_command) = self.notification_receiver.recv().await {
            match notification_command {
                //Whenever a new template is received it is broadcasted across all the downstream nodes connected
                NotifyCmd::SendToAll {
                    template,
                    merkel_branch_coinbase,
                } => {
                    log::info!("Received new template to broadcast to all clients");
                    let template_ref = template.clone();
                    //We will receive the template from the IPC channel and construct a valid job
                    //from the provided template and pass onto the message_reciver in the handle connection for
                    // downstream communication to take place.
                    for (peer_adr, mining_job_arc) in self.job_map_arc.lock().await.iter() {
                        let mut curr_peer_mining_job_map = mining_job_arc.lock().await;
                        //The new job id to be provided while constructing the new job
                        let next_job_id = curr_peer_mining_job_map.get_next_job_id();
                        //Clean Jobs. If true, miners should abort their current work and immediately use the new job, even if it degrades hashrate in the short term. If false, they can still use the current job, but should move to the new one as soon as possible without impacting hashrate.
                        let clean_job = false;
                        let job_notification = Self::construct_job_notification(
                            clean_job,
                            template_ref.clone(),
                            next_job_id,
                            merkel_branch_coinbase.clone(),
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
                                    let job_details = JobDetails {
                                        blocktemplate: template_ref.clone(),
                                        coinbase1: job.coinbase1.clone(),
                                        coinbase2: job.coinbase2.clone(),
                                    };
                                    curr_peer_mining_job_map
                                        .insert_mining_job(job_details)
                                        .await;
                                    //this will change
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
                        //nodes that is write to `TcpStream`
                        let downstream_channel_mapping = downstream_connection_map
                            .lock()
                            .await
                            .downstream_channel_mapping
                            .clone();
                        for (downstream_addr, downstream_channel) in
                            downstream_channel_mapping.iter()
                        {
                            log::info!(
                                "Sending template to downstream at address {}",
                                downstream_addr
                            );
                            downstream_channel.send(job_notification.clone()).await;
                        }
                    }
                }
                //Another notification event to provide the latest possible template available whenever a new peer
                // is connected `subscribed` and `authorized` via stratum protocol
                NotifyCmd::SendLatestTemplateToNewDownstream {
                    new_downstream_addr,
                } => {
                    let latest_template = latest_template_arc.lock().await.to_owned();
                    let latest_template_merkel_branch =
                        latest_template_merkel_branch_arc.lock().await.to_owned();
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
                        latest_template_merkel_branch,
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
                                let job_details = JobDetails {
                                    blocktemplate: latest_template,
                                    coinbase1: job.coinbase1.clone(),
                                    coinbase2: job.coinbase2.clone(),
                                };
                                curr_peer_mining_job_map
                                    .insert_mining_job(job_details)
                                    .await;
                                //this will change
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
                    current_downstream_message_sender
                        .send(job_notification)
                        .await;
                }
            }
        }
        Ok(())
    }
}
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
    pub fn new(
        server_config: StratumServerConfig,
        connection_mapping_arc: Arc<Mutex<ConnectionMapping>>,
    ) -> Self {
        log::info!("Initializing server with config: {:?}", server_config);
        let (downstream_tx, downstream_rx) = mpsc::channel::<String>(32);

        Self {
            stratum_config: server_config,
            downstream_connection_mapping: connection_mapping_arc,
            // downstream_miner: Arc::new(Mutex::new(DownstreamClient::default())),
            // downstream_receiver: downstream_rx,
            // downstream_sender: downstream_tx.clone(),
        }
    }
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
                                Self::handle_connection(self_.clone(),peer_addr,reader,writer,&mut downstream_rx,self_mining_map.clone(),downstream_tx,notification_sender).await;
                             });
                        }
                        Err(error)=>{
                            log::info!("Connection failed: {:?}", error);
                        }
                    }
                }
            }
        }

        Ok(())
    }
    pub async fn handle_connection(
        downstream_client: Arc<Mutex<DownstreamClient>>,
        peer_addr: SocketAddr,
        stream_reader: OwnedReadHalf,
        mut stream_writer: OwnedWriteHalf,
        mut downstream_receiver: &mut mpsc::Receiver<String>,
        mining_job_map: Arc<Mutex<MiningJobMap>>,
        downstream_message_sender: mpsc::Sender<String>,
        notification_sender: mpsc::Sender<NotifyCmd>,
    ) -> Result<(), Box<tokio_util::codec::LinesCodecError>> {
        const MAX_LINE_LENGTH: usize = 2_usize.pow(16);
        ///It can be excessively inefficient to work directly with a AsyncRead instance. A BufReader performs large, infrequent reads on the underlying AsyncRead and maintains an in-memory buffer of the results.
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
                            log::error!("An error occurred while writing to the stream");
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

                             downstream_client.lock().await.handle_client_to_server_request(serde_json::from_str(&line).unwrap(),mining_job_map.clone(),downstream_message_sender.clone(),notification_sender.clone(),peer_addr.to_string()).await;

                        }
                        Some(Err(e)) => {
                            log::error!("Error reading line from {}: {}", peer_addr, e);
                            return Err(Box::new(e));
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
