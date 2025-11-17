use std::collections::HashMap;

use crate::utils::BeadHash;
//Beads fetching will be done with batch size
pub const IBD_BATCH_SIZE: usize = 100;

//Storing tips mapping received from peers during `GetTips`
//that will be flushed out after IBD is done hence no complete dependency
#[derive(Debug)]
pub enum IBDCommands {
    //Updating tips received from various sync peers that will act as the stopping window for IBD
    UpdateIBDTipsCache {
        received_tips: Vec<BeadHash>,
        peer_id: String,
    },
    //Caching the received beadhashes received during `GetBead` request which will be used to fetch and extend beads in batches via `GetBead`
    UpdateIBDGetBeadCache {
        get_bead_response: Vec<BeadHash>,
        peer_id: String,
    },
    //Update the batch offset and fetch newer batch offset window will become [offset*batchsize,(offset*batchsize)+batchsize]
    UpdateAndFetchBatchOffset {
        peer_id: String,
        offset_sender: tokio::sync::oneshot::Sender<usize>,
        batch_size: usize,
    },
    //Fetching the cached Tips
    FetchCachedTips {
        peer_id: String,
        tips_sender: tokio::sync::oneshot::Sender<Vec<BeadHash>>,
    },
    //Fetching cached beadshashes received during GetBeads
    FetchGetBeadCache {
        peer_id: String,
        beadhash_sender: tokio::sync::oneshot::Sender<Vec<BeadHash>>,
    },
}
pub struct IBDManager {
    tips_mapping: HashMap<String, Vec<BeadHash>>,
    batch_mapping: HashMap<String, usize>,
    get_bead_mapping: HashMap<String, Vec<BeadHash>>,
    command_receiver: tokio::sync::mpsc::Receiver<IBDCommands>,
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
            },
            ibd_tx,
        )
    }
    pub async fn handle_ibd_command(&mut self) {
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
                                    error,"Error while initiating batch offset and sending it to request channel"
                                );
                            }
                        }
                    }
                }
                IBDCommands::UpdateIBDGetBeadCache {
                    get_bead_response,
                    peer_id,
                } => {
                    self.get_bead_mapping.insert(peer_id, get_bead_response);
                }
                IBDCommands::UpdateIBDTipsCache {
                    received_tips,
                    peer_id,
                } => {
                    self.tips_mapping.insert(peer_id, received_tips);
                }
                IBDCommands::FetchCachedTips {
                    peer_id,
                    tips_sender,
                } => {
                    if let Some(cached_tips) = self.tips_mapping.get(&peer_id) {
                        match tips_sender.send(cached_tips.clone()) {
                            Ok(_) => {
                                tracing::info!("Cached tips sent successfully to swarm event loop");
                            }
                            Err(_error) => {
                                tracing::error!("Tips not sent");
                            }
                        };
                    };
                }
                IBDCommands::FetchGetBeadCache {
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
                            Err(_error) => {
                                tracing::error!("Beadhashes not sent");
                            }
                        };
                    };
                }
            }
        }
    }
}
