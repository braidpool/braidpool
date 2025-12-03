use std::{collections::HashMap, u64};

use libp2p::PeerId;
use tokio::task::JoinHandle;

use crate::utils::BeadHash;
pub const IBD_BATCH_SIZE: usize = 500;
pub const MAX_IBD_RETRIES: u64 = 10;
pub const IBD_TRIGGER_AFTER: u64 = 20;
/// We wait for incoming beads with the range [current_timestamp,current_timestamp + MAX_IBD_INCOMING_THRESHOLD]
pub const MAX_IBD_INCOMING_THRESHOLD: u64 = 20;

#[derive(Debug)]
pub enum IBDCommands {
    UpdateIBDTipsMapping {
        received_tips: Vec<BeadHash>,
        peer_id: String,
    },
    UpdateIncoming {
        get_bead_response: Vec<BeadHash>,
        peer_id: String,
    },
    UpdateAndFetchBatchOffset {
        peer_id: String,
        offset_sender: tokio::sync::oneshot::Sender<usize>,
        batch_size: usize,
    },
    FetchTips {
        peer_id: String,
        tips_sender: tokio::sync::oneshot::Sender<Vec<BeadHash>>,
    },
    FetchGetBeadMapping {
        peer_id: String,
        beadhash_sender: tokio::sync::oneshot::Sender<Vec<BeadHash>>,
    },
    UpdateTimestampMapping {
        peer_id: String,
        end_timestamp: u64,
    },
    FetchTimestamp {
        peer_id: String,
        timestamp_sender: tokio::sync::oneshot::Sender<u64>,
    },
    FetchAllTimestamps {
        sender: tokio::sync::oneshot::Sender<HashMap<String, u64>>,
    },
    UpdateIncomingBeadMapping {
        peer_id: PeerId,
        handle: Option<JoinHandle<()>>,
        retry_or_not: bool,
    },
    GetIncomingBeadRetryCount {
        peer_id: PeerId,
        retry_sender: tokio::sync::oneshot::Sender<u64>,
    },
    AbortWaitHandle {
        peer_id: PeerId,
    },
}
/// The `IBDManager` is responsible for coordinating all state and bookkeeping
/// required during the Initial Block Download (IBD) phase.
///
/// It receives asynchronous `IBDCommands` through an internal channel and
/// maintains multiple internal mappings used to:
///
/// - Track per-peer batch offsets for batched bead requests  
/// - Store tips in memory received from sync peers  
/// - Store bead in memory responses mapped by peer  
/// - Track per-peer timestamps for sequencing IBD batches  
/// - Maintain retry counts and async handles for incoming bead-processing tasks  
///
/// The manager runs a dedicated event loop (see `run_ibd_handler`) which
/// consumes commands and mutates internal state accordingly.
///
/// This component is intentionally single-threaded (through the event loop),
/// ensuring safe mutation of maps without additional synchronization.
pub struct IBDManager {
    /// Tracks the most recent tips received from each peer during IBD.
    /// (peer_id --> Vec<BeadHash>)
    tips_mapping: HashMap<String, Vec<BeadHash>>,

    /// Tracks the current batch offset for each peer when requesting batched beads.
    /// (peer_id --> current offset)
    batch_mapping: HashMap<String, usize>,

    /// Stores bead hashes obtained by GetBead requests from each peer.
    /// (peer_id --> Vec<BeadHash>)
    get_bead_mapping: HashMap<String, Vec<BeadHash>>,

    /// The internal channel receiver for all IBD-related commands.
    command_receiver: tokio::sync::mpsc::Receiver<IBDCommands>,

    /// Stores the timestamp associated with the last successfully processed batch
    /// for each peer.
    /// (peer_id --> timestamp)
    timestamp_mapping: HashMap<String, u64>,

    /// Tracks retry counts and associated join handles for incoming bead
    /// processing tasks.
    ///
    /// (peer_id --> (retry_count, Option<JoinHandle>))
    ///
    /// A retry count increments when an incoming bead handler must be restarted.
    incoming_bead_mapping: HashMap<PeerId, (u64, Option<JoinHandle<()>>)>,
}
impl IBDManager {
    pub fn new() -> (Self, tokio::sync::mpsc::Sender<IBDCommands>) {
        let (ibd_tx, ibd_rx) = tokio::sync::mpsc::channel::<IBDCommands>(1024);
        (
            Self {
                tips_mapping: HashMap::new(),
                batch_mapping: HashMap::new(),
                get_bead_mapping: HashMap::new(),
                command_receiver: ibd_rx,
                timestamp_mapping: HashMap::new(),
                incoming_bead_mapping: HashMap::new(),
            },
            ibd_tx,
        )
    }
    pub async fn run_ibd_handler(&mut self) {
        while let Some(ibd_command) = self.command_receiver.recv().await {
            match ibd_command {
                IBDCommands::UpdateAndFetchBatchOffset {
                    peer_id,
                    offset_sender,
                    batch_size,
                } => {
                    if let Some(current_offset) = self.batch_mapping.get_mut(&peer_id) {
                        match offset_sender.send(*current_offset) {
                            Ok(_) => {
                                tracing::info!(
                                    "Sending newer offset and updating the current offset"
                                );
                                *current_offset = *current_offset + batch_size;
                            }
                            Err(error) => {
                                tracing::error!(
                                error=?error, "Error while updating and sending it to request channel"
                                );
                            }
                        };
                    } else {
                        self.batch_mapping.insert(peer_id, IBD_BATCH_SIZE);
                        match offset_sender.send(IBD_BATCH_SIZE) {
                            Ok(_) => {
                                tracing::info!("Sent newly initialized offset to request channel");
                            }
                            Err(error) => {
                                tracing::error!(
                                    error=?error,"Error while initiating batch offset and sending it to request channel"
                                );
                            }
                        }
                    }
                }
                IBDCommands::UpdateIncoming {
                    get_bead_response,
                    peer_id,
                } => {
                    self.get_bead_mapping.insert(peer_id, get_bead_response);
                }
                IBDCommands::UpdateIBDTipsMapping {
                    received_tips,
                    peer_id,
                } => {
                    self.tips_mapping.insert(peer_id, received_tips);
                }
                IBDCommands::FetchTips {
                    peer_id,
                    tips_sender,
                } => {
                    if let Some(cached_tips) = self.tips_mapping.get(&peer_id) {
                        match tips_sender.send(cached_tips.clone()) {
                            Ok(_) => {
                                tracing::info!("Cached tips sent successfully to swarm event loop");
                            }
                            Err(error) => {
                                tracing::error!(error=?error,"Tips not sent");
                            }
                        };
                    };
                }
                IBDCommands::FetchGetBeadMapping {
                    peer_id,
                    beadhash_sender,
                } => {
                    if let Some(cached_hashes) = self.get_bead_mapping.get(&peer_id) {
                        match beadhash_sender.send(cached_hashes.clone()) {
                            Ok(_) => {
                                tracing::info!(
                                    "Cached get bead hashes sent successfully to swarm event loop"
                                );
                            }
                            Err(error) => {
                                tracing::error!(error=?error,"Beadhashes not sent");
                            }
                        };
                    };
                }
                IBDCommands::UpdateTimestampMapping {
                    peer_id,
                    end_timestamp,
                } => {
                    if self.timestamp_mapping.contains_key(&peer_id) {
                        if let Some(prev_timestamp) = self.timestamp_mapping.get(&peer_id) {
                            if *prev_timestamp == end_timestamp {
                                tracing::info!("Timestamp already exists");
                            } else {
                                //It is a retry request for IBD can be caused due to failure in any of the case
                                //hence timestamp must be updated
                                self.timestamp_mapping.insert(peer_id, end_timestamp);
                            }
                        };
                    } else {
                        tracing::info!("Timestamp received after receiving last batch of beads requested by peer from sync node");
                        self.timestamp_mapping.insert(peer_id, end_timestamp);
                    }
                }
                IBDCommands::FetchTimestamp {
                    peer_id,
                    timestamp_sender,
                } => {
                    if let Some(current_ts) = self.timestamp_mapping.get(&peer_id) {
                        match timestamp_sender.send(*current_ts) {
                            Ok(_) => {
                                tracing::info!("Fetched existing timestamp for peer");
                            }
                            Err(error) => {
                                tracing::error!(
                                    error=?error,
                                    "Error while sending existing timestamp to request channel"
                                );
                            }
                        }
                    } else {
                        tracing::error!("No timestamp found corresponding to the peer id");
                    }
                }
                IBDCommands::FetchAllTimestamps { sender } => {
                    let timestamps_clone = self.timestamp_mapping.clone();
                    match sender.send(timestamps_clone) {
                        Ok(_) => {
                            tracing::info!("Sent entire timestamp mapping to requester");
                        }
                        Err(error) => {
                            tracing::error!(
                                error=?error,
                                "Error while sending timestamp mapping to requester"
                            );
                        }
                    }
                }
                IBDCommands::UpdateIncomingBeadMapping {
                    peer_id,
                    handle,
                    retry_or_not,
                } => {
                    if self.incoming_bead_mapping.contains_key(&peer_id) {
                        if retry_or_not {
                            if let Some(mapped_tuple) = self.incoming_bead_mapping.get_mut(&peer_id)
                            {
                                //Aborting the previous handle
                                if let Some(ibd_incoming_handle) = &mapped_tuple.1 {
                                    if ibd_incoming_handle.is_finished() {
                                        tracing::info!("Previous IBD incoming handle for peer {} already finished", peer_id);
                                    } else {
                                        ibd_incoming_handle.abort();
                                        tracing::info!(
                                            "Aborted previous IBD incoming handle for peer {}",
                                            peer_id
                                        );
                                    }
                                }
                                //Updating retry count and setting newer handle to None
                                *mapped_tuple = (mapped_tuple.0 + 1, None);
                            }
                        } else {
                            //If it is not a retry then we can use the previously stored value
                            if let Some(mapped_tuple) = self.incoming_bead_mapping.get_mut(&peer_id)
                            {
                                *mapped_tuple = (mapped_tuple.0, handle);
                            }
                        }
                    } else {
                        self.incoming_bead_mapping.insert(peer_id, (0, None));
                    }
                }
                IBDCommands::GetIncomingBeadRetryCount {
                    peer_id,
                    retry_sender,
                } => {
                    let retries = self
                        .incoming_bead_mapping
                        .get(&peer_id)
                        .map(|entry| entry.0)
                        .unwrap_or(u64::MAX);

                    let _ = retry_sender.send(retries);

                    tracing::debug!("Fetched retry count for peer {} -> {}", peer_id, retries);
                }
                IBDCommands::AbortWaitHandle { peer_id } => {
                    if let Some(incoming_mapping) = self.incoming_bead_mapping.get_mut(&peer_id) {
                        if let Some(ibd_wait_handle) = &incoming_mapping.1 {
                            ibd_wait_handle.abort();
                        }
                        incoming_mapping.1 = None;
                    };
                }
            }
        }
    }
}
