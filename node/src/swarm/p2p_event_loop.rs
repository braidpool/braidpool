//! Main event loop for the swarm.
//!
//! This module contains the event dispatch logic that routes swarm events
//! to their appropriate handlers.

use std::time::Duration;

use futures::StreamExt;
use libp2p::{floodsub, identify, kad, ping, request_response, swarm::SwarmEvent, Swarm};
use tokio::sync::mpsc::Receiver;
use tracing::{debug, error, info, warn};

use crate::{
    bead::{BeadRequest, BeadResponse},
    behaviour::{BraidPoolBehaviour, BraidPoolBehaviourEvent},
    ibd_manager::{IBDCommands, IBD_TRIGGER_AFTER, MAX_IBD_RETRIES},
    SwarmCommand,
};

use super::{
    handlers::{
        bead_sync, connection, floodsub as floodsub_handler, identify as identify_handler,
        kademlia, ping as ping_handler,
    },
    SwarmContext,
};

/// Runs the main swarm event loop.
///
/// This function processes swarm events and swarm commands, dispatching
/// them to appropriate handlers.
///
/// # Arguments
/// * `ctx` - The swarm context containing shared state
/// * `swarm` - The libp2p swarm
/// * `cmd_rx` - Receiver for swarm commands
pub async fn run(
    mut ctx: SwarmContext,
    mut swarm: Swarm<BraidPoolBehaviour>,
    mut cmd_rx: Receiver<SwarmCommand>,
) {
    loop {
        tokio::select! {
            //Swarm events
            swarm_event = swarm.select_next_some() => {
                dispatch_swarm_event(&mut ctx, &mut swarm, swarm_event).await;
            }
            //Events other than p2p
            Some(cmd) = cmd_rx.recv() => {
                handle_swarm_command(&mut ctx, &mut swarm, cmd).await;
            }
        }
    }
}

/// Dispatches a swarm event to the appropriate handler.
async fn dispatch_swarm_event(
    ctx: &mut SwarmContext,
    swarm: &mut Swarm<BraidPoolBehaviour>,
    event: SwarmEvent<BraidPoolBehaviourEvent>,
) {
    match event {
        SwarmEvent::Behaviour(BraidPoolBehaviourEvent::Kademlia(kad::Event::RoutingUpdated {
            peer,
            is_new_peer,
            addresses,
            bucket_range,
            old_peer,
        })) => {
            kademlia::handle_routing_updated(peer, is_new_peer, addresses, bucket_range, old_peer);
        }

        SwarmEvent::Behaviour(BraidPoolBehaviourEvent::Kademlia(
            kad::Event::OutboundQueryProgressed { result, .. },
        )) => {
            kademlia::handle_outbound_query(result);
        }

        SwarmEvent::Behaviour(BraidPoolBehaviourEvent::BeadAnnounce(
            floodsub::FloodsubEvent::Subscribed { peer_id, topic },
        )) => {
            floodsub_handler::handle_subscribed(peer_id, topic);
        }

        SwarmEvent::Behaviour(BraidPoolBehaviourEvent::BeadAnnounce(
            floodsub::FloodsubEvent::Unsubscribed { peer_id, topic },
        )) => {
            floodsub_handler::handle_unsubscribed(peer_id, topic);
        }

        SwarmEvent::Behaviour(BraidPoolBehaviourEvent::BeadAnnounce(
            floodsub::FloodsubEvent::Message(message),
        )) => {
            floodsub_handler::handle_message(ctx, swarm, message).await;
        }

        SwarmEvent::Behaviour(BraidPoolBehaviourEvent::Identify(identify::Event::Sent {
            peer_id,
            ..
        })) => {
            identify_handler::handle_sent(peer_id);
        }

        SwarmEvent::Behaviour(BraidPoolBehaviourEvent::Identify(identify::Event::Received {
            peer_id,
            info,
            ..
        })) => {
            identify_handler::handle_received(peer_id, info);
        }

        SwarmEvent::Behaviour(BraidPoolBehaviourEvent::Identify(identify::Event::Error {
            peer_id,
            error,
            ..
        })) => {
            identify_handler::handle_error(peer_id, error);
        }

        SwarmEvent::Behaviour(BraidPoolBehaviourEvent::Ping(ping::Event {
            peer, result, ..
        })) => match result {
            Ok(latency) => {
                ping_handler::handle_ping_success(peer, latency, &ctx.peer_manager).await;
            }
            Err(err) => {
                ping_handler::handle_ping_failure(peer, err);
            }
        },

        SwarmEvent::ConnectionEstablished {
            peer_id, endpoint, ..
        } => {
            connection::handle_connection_established(swarm, &ctx.peer_manager, peer_id, &endpoint)
                .await;
        }

        SwarmEvent::ConnectionClosed {
            peer_id,
            connection_id,
            endpoint,
            num_established,
            cause,
        } => {
            connection::handle_connection_closed(
                swarm,
                &ctx.peer_manager,
                peer_id,
                connection_id,
                &endpoint,
                num_established,
                cause.as_ref(),
            )
            .await;
        }

        SwarmEvent::Behaviour(BraidPoolBehaviourEvent::BeadSync(
            request_response::Event::Message {
                peer,
                message,
                connection_id,
            },
        )) => {
            info!(
                peer = %peer,
                connection = ?connection_id,
                "Bead sync message"
            );

            match message {
                request_response::Message::Request {
                    request, channel, ..
                } => {
                    dispatch_bead_sync_request(ctx, swarm, peer, request, channel).await;
                }
                request_response::Message::Response { response, .. } => {
                    dispatch_bead_sync_response(ctx, swarm, peer, response).await;
                }
            }
        }

        SwarmEvent::NewListenAddr { address, .. } => {
            info!(address = ?address, "P2P listening on address");
        }

        other => {
            debug!(event = ?other, "Other swarm event");
        }
    }
}

/// Dispatches a BeadSync(IBD) request to the appropriate handler.
async fn dispatch_bead_sync_request(
    ctx: &SwarmContext,
    swarm: &mut Swarm<BraidPoolBehaviour>,
    _peer: libp2p::PeerId,
    request: BeadRequest,
    channel: request_response::ResponseChannel<BeadResponse>,
) {
    match request {
        BeadRequest::GetBeads(hashes) => {
            bead_sync::handle_get_beads(ctx, swarm, hashes, channel).await;
        }
        BeadRequest::GetTips => {
            bead_sync::handle_get_tips(ctx, swarm, channel).await;
        }
        BeadRequest::GetGenesis => {
            bead_sync::handle_get_genesis(ctx, swarm, channel).await;
        }
        BeadRequest::GetAllBeads => {
            bead_sync::handle_get_all_beads(ctx, swarm, channel).await;
        }
        BeadRequest::GetBeadsAfter(hashes) => {
            bead_sync::handle_get_beads_after(ctx, swarm, hashes, channel).await;
        }
    }
}

/// Dispatches a BeadSync(IBD) response to the appropriate handler.
async fn dispatch_bead_sync_response(
    ctx: &mut SwarmContext,
    swarm: &mut Swarm<BraidPoolBehaviour>,
    peer: libp2p::PeerId,
    response: BeadResponse,
) {
    match response {
        BeadResponse::Beads(beads) | BeadResponse::GetAllBeads(beads) => {
            bead_sync::handle_beads_response(ctx, swarm, peer, beads).await;
        }
        BeadResponse::GetBeadsAfter(hashes) => {
            bead_sync::handle_get_beads_after_response(ctx, swarm, peer, hashes).await;
        }
        BeadResponse::Tips(tips) => {
            bead_sync::handle_tips_response(ctx, swarm, peer, tips).await;
        }
        BeadResponse::Genesis(genesis) => {
            bead_sync::handle_genesis_response(ctx, swarm, peer, genesis).await;
        }
        BeadResponse::Error(error) => {
            bead_sync::handle_error_response(swarm, peer, error);
        }
    }
}

/// Handles a swarm command.
async fn handle_swarm_command(
    ctx: &mut SwarmContext,
    swarm: &mut Swarm<BraidPoolBehaviour>,
    command: SwarmCommand,
) {
    match command {
        SwarmCommand::PropagateValidBead { bead_bytes } => {
            let topic = libp2p::floodsub::Topic::new(crate::behaviour::BRAIDPOOL_TOPIC);
            swarm
                .behaviour_mut()
                .bead_announce
                .publish(topic.clone(), bead_bytes);
            info!(topic = ?topic, "Published bead to floodsub topic");
        }

        SwarmCommand::InitiateIBD => {
            initiate_ibd(ctx, swarm).await;
        }
    }
}

/// Initiates the Initial Block Download process.
async fn initiate_ibd(ctx: &mut SwarmContext, swarm: &mut Swarm<BraidPoolBehaviour>) {
    info!("Initiating IBD - selecting lowest latency peer");

    let peer_ids = {
        let peer_manager = ctx.peer_manager.read().await;
        peer_manager.get_top_k_peers_for_propagation(1)
    };

    if peer_ids.is_empty() {
        warn!("No peers available for sync");
        schedule_ibd_retry(ctx.swarm_cmd_tx.clone());
        return;
    }

    let mut sync_request_sent = false;

    for peer in peer_ids {
        // Check retry count
        let (retry_tx, retry_rx) = tokio::sync::oneshot::channel();

        if let Err(e) = ctx
            .ibd_tx
            .send(IBDCommands::GetIncomingBeadRetryCount {
                peer_id: peer,
                retry_sender: retry_tx,
            })
            .await
        {
            error!(error = ?e, "Failed to get retry count");
            continue;
        }

        let retry_count = match retry_rx.await {
            Ok(count) => count,
            Err(e) => {
                error!(error = ?e, "Failed to receive retry count");
                continue;
            }
        };

        if retry_count >= MAX_IBD_RETRIES && retry_count != u64::MAX {
            warn!(peer = ?peer, retries = retry_count, "Peer exceeded retry limit");
            continue;
        }

        // Update incoming bead mapping
        let is_retry = retry_count != u64::MAX;

        if let Err(e) = ctx
            .ibd_tx
            .send(IBDCommands::UpdateIncomingBeadMapping {
                peer_id: peer,
                retry_or_not: is_retry,
                handle: None,
            })
            .await
        {
            error!(error = ?e, "Failed to update incoming mapping");
            continue;
        }

        // Send GetTips request
        let request = BeadRequest::GetTips;
        swarm.behaviour_mut().bead_sync.send_request(&peer, request);

        info!(peer = ?peer, "IBD started with peer");
        sync_request_sent = true;
        break;
    }

    if !sync_request_sent {
        warn!("All sync peers exceeded retry limits");
        schedule_ibd_retry(ctx.swarm_cmd_tx.clone());
    }
}

/// Schedules an IBD retry after a delay.
fn schedule_ibd_retry(cmd_tx: tokio::sync::mpsc::Sender<SwarmCommand>) {
    tokio::spawn(async move {
        tokio::time::sleep(Duration::from_secs(IBD_TRIGGER_AFTER)).await;
        if let Err(e) = cmd_tx.send(SwarmCommand::InitiateIBD).await {
            error!(error = ?e, "Failed to schedule IBD retry");
        } else {
            info!("Retrying IBD after delay");
        }
    });
}
