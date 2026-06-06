//! FloodSub (bead announcement) event handlers.

use bitcoin::consensus::encode::deserialize;
use libp2p::{floodsub::FloodsubMessage, PeerId, Swarm};
use tracing::{error, info, warn};

use crate::{
    bead::{Bead, BeadHashes, BeadRequest},
    behaviour::BraidPoolBehaviour,
    braid::AddBeadStatus,
    ibd_manager::IBDCommands,
    swarm::{
        config::LATENCY_ALPHA, handlers::bead_processing::process_incoming_bead, SwarmContext,
    },
    SwarmCommand,
};

/// Handles a subscription event.
pub fn handle_subscribed(peer_id: PeerId, topic: libp2p::floodsub::Topic) {
    info!(
        peer = ?peer_id,
        topic = ?topic,
        "Peer subscribed to topic"
    );
}

/// Handles an unsubscription event.
pub fn handle_unsubscribed(peer_id: PeerId, topic: libp2p::floodsub::Topic) {
    info!(
        peer = ?peer_id,
        topic = ?topic,
        "Peer unsubscribed from topic"
    );
}

/// Handles a FloodSub message (bead announcement).
///
/// This is the main handler for incoming beads via p2p nodes.
/// Behavior differs based on whether node is in IBD mode.
pub async fn handle_message(
    ctx: &mut SwarmContext,
    swarm: &mut Swarm<BraidPoolBehaviour>,
    message: FloodsubMessage,
) {
    info!(
        topics = ?message.topics,
        source = ?message.source,
        size_bytes = %message.data.len(),
        "Floodsub message received"
    );

    // Deserialize the bead
    let bead: Bead = match deserialize::<Bead>(&message.data) {
        Ok(b) => {
            info!(
                hash = %b.block_header.block_hash(),
                "Received bead"
            );
            b
        }
        Err(e) => {
            error!(error = %e, "Failed to deserialize bead");
            return;
        }
    };

    if ctx.is_in_ibd() {
        handle_message_during_ibd(ctx, swarm, &bead, message.source).await;
    } else {
        handle_message_normal(ctx, swarm, &bead, message.source).await;
    }
}

/// Handles bead message during normal operation (not IBD).
async fn handle_message_normal(
    ctx: &mut SwarmContext,
    swarm: &mut Swarm<BraidPoolBehaviour>,
    bead: &Bead,
    source: PeerId,
) {
    let mut braid_guard = ctx.braid.write().await;
    let result = process_incoming_bead(ctx, &mut braid_guard, bead, source).await;

    match result.status {
        AddBeadStatus::ParentsNotYetReceived => {
            request_parents(ctx, swarm, bead).await;
        }
        AddBeadStatus::InvalidBead => {
            ctx.peer_manager
                .write()
                .await
                .penalize_for_invalid_bead(&source);
        }
        AddBeadStatus::BeadAdded => {
            ctx.peer_manager.write().await.update_score(&source, 1.0);
        }
        _ => {}
    }
}

/// Handles bead message during Initial Block Download.
async fn handle_message_during_ibd(
    ctx: &mut SwarmContext,
    swarm: &mut Swarm<BraidPoolBehaviour>,
    bead: &Bead,
    source: PeerId,
) {
    // Process bead
    let (status, bead_persisted) = {
        let mut braid_guard = ctx.braid.write().await;
        let result = process_incoming_bead(ctx, &mut braid_guard, bead, source).await;
        (result.status, result.persisted)
    };
    // Guard is dropped here
    let broadcast_ts = bead.uncommitted_metadata.broadcast_timestamp.to_u32();

    match &status {
        AddBeadStatus::ParentsNotYetReceived => {
            request_parents(ctx, swarm, bead).await;
        }
        AddBeadStatus::InvalidBead => {
            ctx.peer_manager
                .write()
                .await
                .penalize_for_invalid_bead(&source);
        }
        AddBeadStatus::BeadAdded => {
            if bead_persisted {
                ctx.peer_manager.write().await.update_score(&source, 1.0);
            }
        }
        _ => {}
    }

    // Fetch timestamp map from IBD manager
    let (ts_tx, ts_rx) = tokio::sync::oneshot::channel();
    if let Err(e) = ctx
        .ibd_tx
        .send(IBDCommands::FetchAllTimestamps { sender: ts_tx })
        .await
    {
        warn!("Failed to request timestamp map: {:?}", e);
        return;
    }

    let timestamp_map = match ts_rx.await {
        Ok(map) => map,
        Err(_) => {
            error!("Failed to receive timestamp map");
            return;
        }
    };

    // Check timestamp thresholds for each sync peer
    for (sync_peer_str, ibd_ts) in timestamp_map.iter() {
        let threshold = *ibd_ts + LATENCY_ALPHA * 10;

        let sync_peer_id = match sync_peer_str.parse::<PeerId>() {
            Ok(id) => id,
            Err(e) => {
                error!(sync_peer = %sync_peer_str, error = %e, "Failed to parse sync peer ID");
                continue;
            }
        };

        if broadcast_ts < threshold as u32 {
            info!(
                broadcast_ts = ?broadcast_ts,
                threshold = ?threshold,
                "Incoming bead during IBD within threshold"
            );

            match status {
                AddBeadStatus::InvalidBead | AddBeadStatus::ParentsNotYetReceived => {
                    // Abort IBD handler for this sync peer and reinitiate
                    abort_and_reinitiate_ibd(ctx, sync_peer_id).await;
                }
                AddBeadStatus::BeadAdded | AddBeadStatus::DagAlreadyContainsBead => {
                    // IBD can complete
                    ctx.set_ibd(false);
                }
            }
        } else {
            // Timestamp exceeded threshold, IBD complete
            ctx.set_ibd(false);
        }
    }
}

/// Requests missing parent beads from peers.
async fn request_parents(ctx: &SwarmContext, swarm: &mut Swarm<BraidPoolBehaviour>, bead: &Bead) {
    if let Some(peer) = ctx.get_sync_peer().await {
        let parent_hashes: Vec<_> = bead.committed_metadata.parents.iter().cloned().collect();
        swarm
            .behaviour_mut()
            .bead_sync
            .send_request(&peer, BeadRequest::GetBeads(BeadHashes(parent_hashes)));
    } else {
        warn!(
            parent_count = %bead.committed_metadata.parents.len(),
            "Insufficient peers for bead sync"
        );
    }
}

/// Aborts IBD handler for a sync peer and reinitiates IBD.
async fn abort_and_reinitiate_ibd(ctx: &SwarmContext, sync_peer: PeerId) {
    // Abort the wait handle
    if let Err(e) = ctx
        .ibd_tx
        .send(IBDCommands::AbortWaitHandle { peer_id: sync_peer })
        .await
    {
        error!(error = ?e, "Failed to send abort handler command");
    } else {
        warn!("Abort handle sent for sync peer");
    }

    // Reinitiate IBD
    if let Err(e) = ctx.swarm_cmd_tx.send(SwarmCommand::InitiateIBD).await {
        error!(error = ?e, "Failed to reinitiate IBD");
    } else {
        warn!("Reinitiating IBD");
    }
}
