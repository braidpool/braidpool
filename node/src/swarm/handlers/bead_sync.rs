//! BeadSync request/response protocol handlers.

use std::{
    collections::HashSet,
    time::{Duration, SystemTime, UNIX_EPOCH},
};

use libp2p::{request_response::ResponseChannel, PeerId, Swarm};
use tracing::{debug, error, info, warn};

use crate::{
    bead::{BeadHashes, BeadRequest, BeadResponse, BeadSyncError, Beads},
    behaviour::BraidPoolBehaviour,
    braid::{AddBeadStatus, GenesisCheckStatus},
    db::{db_handlers::prepare_bead_tuple_data, BraidpoolDBTypes, InsertTupleTypes},
    ibd_manager::{IBDCommands, IBD_BATCH_SIZE, MAX_IBD_INCOMING_THRESHOLD},
    swarm::SwarmContext,
    utils::BeadHash,
    SwarmCommand,
};

/// Handles a GetBeads request - returns beads for the requested hashes.
pub async fn handle_get_beads(
    ctx: &SwarmContext,
    swarm: &mut Swarm<BraidPoolBehaviour>,
    hashes: BeadHashes,
    channel: ResponseChannel<BeadResponse>,
) {
    let mut beads = Vec::new();
    {
        let braid_lock = ctx.braid.read().await;
        for hash in hashes.iter() {
            if let Some(index) = braid_lock.bead_index_mapping.get(hash) {
                if let Some(bead) = braid_lock.beads.get(*index) {
                    beads.push(bead.clone());
                }
            }
        }
    }
    swarm.behaviour_mut().respond_with_beads(channel, beads);
}

/// Handles a GetTips request - returns current DAG tips.
pub async fn handle_get_tips(
    ctx: &SwarmContext,
    swarm: &mut Swarm<BraidPoolBehaviour>,
    channel: ResponseChannel<BeadResponse>,
) {
    let tips;
    {
        let braid_lock = ctx.braid.read().await;
        tips = braid_lock
            .tips
            .iter()
            .filter_map(|index| braid_lock.beads.get(*index))
            .map(|bead| bead.block_header.block_hash())
            .collect();
    }
    swarm.behaviour_mut().respond_with_tips(channel, tips);
}

/// Handles a GetGenesis request - returns genesis beads.
pub async fn handle_get_genesis(
    ctx: &SwarmContext,
    swarm: &mut Swarm<BraidPoolBehaviour>,
    channel: ResponseChannel<BeadResponse>,
) {
    let genesis;
    {
        let braid_lock = ctx.braid.read().await;
        genesis = braid_lock
            .genesis_beads
            .iter()
            .filter_map(|index| braid_lock.beads.get(*index))
            .map(|bead| bead.block_header.block_hash())
            .collect();
    }
    swarm.behaviour_mut().respond_with_genesis(channel, genesis);
}

/// Handles a GetAllBeads request - returns all beads in the DAG.
pub async fn handle_get_all_beads(
    ctx: &SwarmContext,
    swarm: &mut Swarm<BraidPoolBehaviour>,
    channel: ResponseChannel<BeadResponse>,
) {
    let all_beads;
    {
        let braid_lock = ctx.braid.read().await;
        all_beads = braid_lock.beads.iter().cloned().collect();
    }
    swarm.behaviour_mut().respond_with_beads(channel, all_beads);
}

/// Handles a GetBeadsAfter request - returns bead hashes after the given tips.
pub async fn handle_get_beads_after(
    ctx: &SwarmContext,
    swarm: &mut Swarm<BraidPoolBehaviour>,
    hashes: BeadHashes,
    channel: ResponseChannel<BeadResponse>,
) {
    let beads = ctx.braid.read().await.get_beads_after(hashes.into());

    if let Some(response_beads) = beads {
        let bead_hashes: Vec<BeadHash> = response_beads
            .into_iter()
            .map(|bead| bead.block_header.block_hash())
            .collect();
        swarm
            .behaviour_mut()
            .respond_with_beadhashes(channel, bead_hashes);
    } else {
        swarm
            .behaviour_mut()
            .respond_with_error(channel, BeadSyncError::BeadHashNotFound);
    }
}

/// Handles a Beads response during IBD.
pub async fn handle_beads_response(
    ctx: &mut SwarmContext,
    swarm: &mut Swarm<BraidPoolBehaviour>,
    peer: PeerId,
    beads: Beads,
) {
    // Fetch cached bead hashes from IBD manager
    let (beads_tx, beads_rx) = tokio::sync::oneshot::channel::<Vec<BeadHash>>();

    if let Err(e) = ctx
        .ibd_tx
        .send(IBDCommands::FetchGetBeadMapping {
            peer_id: peer.to_string(),
            beadhash_sender: beads_tx,
        })
        .await
    {
        error!(error = ?e.0, "Failed to fetch bead mapping from IBD handler");
        reinitiate_ibd(ctx).await;
        return;
    }

    let pruned_beads = match beads_rx.await {
        Ok(beads) => beads,
        Err(e) => {
            error!(error = ?e, "Failed to receive cached beads");
            reinitiate_ibd(ctx).await;
            return;
        }
    };

    // Process each bead
    for bead in beads.into_iter() {
        let mut braid_data = ctx.braid.write().await;
        let status = braid_data.extend(&bead);
        let bead_hash = bead.block_header.block_hash();

        match status {
            AddBeadStatus::InvalidBead => {
                ctx.peer_manager
                    .write()
                    .await
                    .penalize_for_invalid_bead(&peer);
            }
            AddBeadStatus::BeadAdded => {
                let bead_id = match braid_data.bead_index_mapping.get(&bead_hash) {
                    Some(id) => *id,
                    None => {
                        error!(bead_hash = ?bead_hash, "Bead ID not found");
                        continue;
                    }
                };

                let (txs_json, relative_json, parent_timestamp_json) = match prepare_bead_tuple_data(
                    &braid_data.beads,
                    &braid_data.bead_index_mapping,
                    &bead,
                ) {
                    Ok(tuples) => tuples,
                    Err(e) => {
                        error!(error = ?e, "Failed to prepare tuple data");
                        continue;
                    }
                };

                ctx.peer_manager.write().await.update_score(&peer, 1.0);

                if let Err(e) = ctx
                    .db_tx
                    .send(BraidpoolDBTypes::InsertTupleTypes {
                        query: InsertTupleTypes::InsertBeadSequentially {
                            bead_to_insert: bead,
                            txs_json,
                            relative_json,
                            parent_timestamp_json,
                            bead_id,
                        },
                    })
                    .await
                {
                    error!(error = ?e.0, "Failed to send bead to database");
                } else {
                    debug!(bead_hash = ?bead_hash, "Bead persisted");
                }
            }
            _ => {}
        }
    }

    // Request next batch
    request_next_batch(ctx, swarm, peer, &pruned_beads).await;
}

/// Handles a GetBeadsAfter response - receives bead hashes to fetch.
pub async fn handle_get_beads_after_response(
    ctx: &mut SwarmContext,
    swarm: &mut Swarm<BraidPoolBehaviour>,
    peer: PeerId,
    bead_hashes: BeadHashes,
) {
    // Fetch cached tips from IBD manager
    let (tips_tx, tips_rx) = tokio::sync::oneshot::channel::<Vec<BeadHash>>();

    if let Err(e) = ctx
        .ibd_tx
        .send(IBDCommands::FetchTips {
            peer_id: peer.to_string(),
            tips_sender: tips_tx,
        })
        .await
    {
        error!(error = ?e, "Failed to fetch tips");
        reinitiate_ibd(ctx).await;
        return;
    }

    let received_tips = match tips_rx.await {
        Ok(tips) => tips,
        Err(e) => {
            error!(error = ?e, "Failed to receive tips");
            reinitiate_ibd(ctx).await;
            return;
        }
    };

    // Prune hashes up to our tips
    let tips_set: HashSet<_> = received_tips.into_iter().collect();
    let mut found_tips = HashSet::new();
    let mut pruned = Vec::new();

    for hash in bead_hashes.0 {
        if tips_set.contains(&hash) {
            found_tips.insert(hash.clone());
        }
        pruned.push(hash);
        if found_tips.len() == tips_set.len() {
            break;
        }
    }

    // Cache pruned hashes
    if let Err(e) = ctx
        .ibd_tx
        .send(IBDCommands::UpdateIncoming {
            get_bead_response: pruned.clone(),
            peer_id: peer.to_string(),
        })
        .await
    {
        error!(error = ?e, "Failed to cache pruned hashes");
        reinitiate_ibd(ctx).await;
        return;
    }

    // Request first batch of beads
    let batch_end = std::cmp::min(IBD_BATCH_SIZE, pruned.len());
    swarm
        .behaviour_mut()
        .request_beads(peer, &pruned[..batch_end].to_vec());
}

/// Handles a Tips response during IBD.
pub async fn handle_tips_response(
    ctx: &mut SwarmContext,
    swarm: &mut Swarm<BraidPoolBehaviour>,
    peer: PeerId,
    tips: BeadHashes,
) {
    info!(tips = ?tips, tip_count = %tips.len(), "Received braid tips");

    // Initialize batch offset
    let (batch_tx, batch_rx) = tokio::sync::oneshot::channel::<usize>();
    if let Err(e) = ctx
        .ibd_tx
        .send(IBDCommands::UpdateAndFetchBatchOffset {
            peer_id: peer.to_string(),
            offset_sender: batch_tx,
            batch_size: IBD_BATCH_SIZE,
        })
        .await
    {
        error!(error = ?e, "Failed to initialize batch offset");
        return;
    }

    if let Err(e) = batch_rx.await {
        error!(error = ?e, "Failed to receive batch offset");
        return;
    }

    // Check if we already have these tips
    let braid_data = ctx.braid.read().await;
    let bead_hash_set: HashSet<BeadHash> = braid_data
        .beads
        .iter()
        .map(|b| b.block_header.block_hash())
        .collect();

    let already_synced = tips.iter().all(|tip| bead_hash_set.contains(tip));

    if already_synced {
        info!("Peer already synced to tip");
        ctx.set_ibd(false);
        return;
    }

    // Cache the received tips
    if let Err(e) = ctx
        .ibd_tx
        .send(IBDCommands::UpdateIBDTipsMapping {
            received_tips: tips.0,
            peer_id: peer.to_string(),
        })
        .await
    {
        error!(error = ?e, "Failed to cache tips");
        return;
    }

    // Get our current tips and request beads after them
    let current_tip_hashes: Vec<_> = braid_data
        .tips
        .iter()
        .filter_map(|idx| braid_data.beads.get(*idx))
        .map(|bead| bead.block_header.block_hash())
        .collect();

    drop(braid_data);

    let request = BeadRequest::GetBeadsAfter(BeadHashes(current_tip_hashes));
    swarm.behaviour_mut().bead_sync.send_request(&peer, request);
}

/// Handles a Genesis response.
pub async fn handle_genesis_response(
    ctx: &SwarmContext,
    swarm: &mut Swarm<BraidPoolBehaviour>,
    peer: PeerId,
    genesis: BeadHashes,
) {
    info!(genesis = ?genesis, "Received genesis beads");

    let status = {
        let braid_lock = ctx.braid.read().await;
        braid_lock.check_genesis_beads(&genesis.0)
    };

    match status {
        GenesisCheckStatus::GenesisBeadsValid => {
            info!("Genesis beads are valid");
        }
        GenesisCheckStatus::MissingGenesisBead => {
            warn!(peer = %peer, "Missing genesis bead");
            swarm.behaviour_mut().request_beads(peer, &genesis.0);
        }
        GenesisCheckStatus::GenesisBeadsCountMismatch => {
            warn!(
                received = %genesis.0.len(),
                peer = %peer,
                "Genesis bead count mismatch"
            );
        }
    }
}

/// Handles a sync error response.
pub fn handle_error_response(
    swarm: &mut Swarm<BraidPoolBehaviour>,
    peer: PeerId,
    error: BeadSyncError,
) {
    match error {
        BeadSyncError::GenesisMismatch => {
            warn!("Genesis mismatch - requesting genesis");
            swarm.behaviour_mut().request_genesis(peer);
        }
        BeadSyncError::BeadHashNotFound => {
            warn!("Requested bead hashes not found");
        }
    }
}

/// Requests the next batch of beads during IBD.
async fn request_next_batch(
    ctx: &mut SwarmContext,
    swarm: &mut Swarm<BraidPoolBehaviour>,
    peer: PeerId,
    pruned_beads: &[BeadHash],
) {
    // Get next batch offset
    let (batch_tx, batch_rx) = tokio::sync::oneshot::channel::<usize>();

    if let Err(e) = ctx
        .ibd_tx
        .send(IBDCommands::UpdateAndFetchBatchOffset {
            peer_id: peer.to_string(),
            offset_sender: batch_tx,
            batch_size: IBD_BATCH_SIZE,
        })
        .await
    {
        error!(error = ?e, "Failed to update batch offset");
        reinitiate_ibd(ctx).await;
        return;
    }

    let offset = match batch_rx.await {
        Ok(o) => o,
        Err(e) => {
            error!(error = ?e, "Failed to receive batch offset");
            reinitiate_ibd(ctx).await;
            return;
        }
    };

    if offset < pruned_beads.len() {
        let end = std::cmp::min(offset + IBD_BATCH_SIZE, pruned_beads.len());
        info!("Requesting beads batch {}..{}", offset, end);
        swarm
            .behaviour_mut()
            .request_beads(peer, &pruned_beads[offset..end].to_vec());
    } else {
        // IBD complete for this peer
        info!(peer = %peer, "IBD completed with peer");
        complete_ibd(ctx, peer).await;
    }
}

/// Marks IBD as complete and sets up incoming bead watcher.
async fn complete_ibd(ctx: &SwarmContext, peer: PeerId) {
    let current_time = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_secs())
        .unwrap_or_else(|e| {
            error!(error = %e, "System time error");
            0
        });

    if let Err(e) = ctx
        .ibd_tx
        .send(IBDCommands::UpdateTimestampMapping {
            peer_id: peer.to_string(),
            end_timestamp: current_time,
        })
        .await
    {
        error!(error = ?e, "Failed to update timestamp mapping");
        return;
    }

    // Spawn watcher task for incoming beads
    let ibd_spinlock = ctx.ibd_spinlock.clone();
    let ibd_tx = ctx.ibd_tx.clone();

    let incoming_handler = tokio::spawn(async move {
        tokio::time::sleep(Duration::from_secs(MAX_IBD_INCOMING_THRESHOLD)).await;
        if ibd_spinlock.load(std::sync::atomic::Ordering::SeqCst) {
            ibd_spinlock.store(false, std::sync::atomic::Ordering::SeqCst);
            warn!("IBD incoming threshold exceeded, setting IBD complete");
        }
    });

    if let Err(e) = ibd_tx
        .send(IBDCommands::UpdateIncomingBeadMapping {
            peer_id: peer,
            retry_or_not: false,
            handle: Some(incoming_handler),
        })
        .await
    {
        error!(error = ?e, "Failed to register incoming handler");
    }
}

/// Reinitiates IBD process.
async fn reinitiate_ibd(ctx: &SwarmContext) {
    if let Err(e) = ctx.swarm_cmd_tx.send(SwarmCommand::InitiateIBD).await {
        error!(error = ?e, "Failed to reinitiate IBD");
    } else {
        warn!("Reinitiating IBD");
    }
}
