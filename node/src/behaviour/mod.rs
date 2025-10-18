use crate::bead::{Bead, BeadCodec, BeadRequest, BeadResponse};
use crate::utils::BeadHash;
use libp2p::floodsub;
use libp2p::{
    identify,
    identity::Keypair,
    kad::{self, store::MemoryStore},
    ping,
    request_response::{self, OutboundRequestId, ResponseChannel},
    swarm::NetworkBehaviour,
    PeerId, StreamProtocol,
};
use std::collections::HashSet;
use std::{error::Error, time::Duration};

// Protocol names
pub const KADPROTOCOLNAME: StreamProtocol = StreamProtocol::new("/braidpool/kad/1.0.0");
pub const IDENTIFYPROTOCOLNAME: StreamProtocol = StreamProtocol::new("/braidpool/identify/1.0.0");
pub const BEAD_SYNC_PROTOCOL: StreamProtocol = StreamProtocol::new("/braidpool/bead-sync/1.0.0");
pub const BEAD_ANNOUNCE_PROTOCOL: StreamProtocol = StreamProtocol::new("/floodsub/1.0.0");
pub const BRAIDPOOL_TOPIC: &str = "braidpool_channel";

// Configuration for the request-response protocol
#[derive(Debug, Clone)]
pub struct BeadSyncConfig {
    pub request_timeout: Duration,
    pub max_concurrent_requests: usize,
}

impl Default for BeadSyncConfig {
    fn default() -> Self {
        Self {
            request_timeout: Duration::from_secs(30),
            max_concurrent_requests: 50,
        }
    }
}
#[derive(NetworkBehaviour)]
//Custom behaviour for braidpool
pub struct BraidPoolBehaviour {
    pub kademlia: kad::Behaviour<MemoryStore>,
    pub identify: identify::Behaviour,
    pub ping: ping::Behaviour,
    pub bead_sync: request_response::Behaviour<BeadCodec>,
    pub bead_announce: floodsub::Floodsub,
}

impl BraidPoolBehaviour {
    pub fn new(local_key: &Keypair) -> Result<BraidPoolBehaviour, Box<dyn Error>> {
        //initializing the store for kademlia based DHT
        let store = MemoryStore::new(local_key.public().to_peer_id());
        //custom kademlia protocol
        let mut kad_config = kad::Config::new(KADPROTOCOLNAME);
        kad_config.set_query_timeout(tokio::time::Duration::from_secs(60));
        //Querying the boot node for finding the neareast neigbor set up for 10 minutes
        //dynamic value can be changed not to small though
        kad_config.set_periodic_bootstrap_interval(Some(Duration::from_secs(600)));
        //custom kad configuration
        let kademlia_behaviour =
            kad::Behaviour::with_config(local_key.public().to_peer_id(), store, kad_config);
        //identify protocol configuration
        let identify_config =
            identify::Config::new(IDENTIFYPROTOCOLNAME.to_string(), local_key.public());
        let identify_behaviour = identify::Behaviour::new(identify_config);
        let ping_config = ping::Config::default()
            .with_timeout(Duration::from_secs(3600))
            .with_interval(Duration::from_secs(60));
        let ping_behaviour = ping::Behaviour::new(ping_config.clone());

        // Initialize bead download behaviour
        let bead_sync_config = BeadSyncConfig::default();
        let bead_sync = request_response::Behaviour::new(
            [(BEAD_SYNC_PROTOCOL, request_response::ProtocolSupport::Full)],
            request_response::Config::default()
                .with_request_timeout(bead_sync_config.request_timeout)
                .with_max_concurrent_streams(bead_sync_config.max_concurrent_requests),
        );
        let bead_announce_config = floodsub::FloodsubConfig::new(local_key.public().to_peer_id());
        let bead_announce = floodsub::Floodsub::from_config(bead_announce_config);

        let braidpool_behaviour = BraidPoolBehaviour {
            identify: identify_behaviour,
            ping: ping_behaviour,
            kademlia: kademlia_behaviour,
            bead_sync,
            bead_announce: bead_announce,
        };

        return Ok(braidpool_behaviour);
    }

    // Request beads from a peer
    pub fn request_beads(&mut self, peer: PeerId, hashes: HashSet<BeadHash>) -> OutboundRequestId {
        self.bead_sync
            .send_request(&peer, BeadRequest::GetBeads(hashes))
    }

    // Request tips from a peer
    pub fn request_tips(&mut self, peer: PeerId) -> OutboundRequestId {
        self.bead_sync.send_request(&peer, BeadRequest::GetTips)
    }

    // Request genesis from a peer
    pub fn request_genesis(&mut self, peer: PeerId) -> OutboundRequestId {
        self.bead_sync.send_request(&peer, BeadRequest::GetGenesis)
    }

    // Respond to a bead request
    pub fn respond_with_beads(&mut self, channel: ResponseChannel<BeadResponse>, beads: Vec<Bead>) {
        self.bead_sync
            .send_response(channel, BeadResponse::Beads(beads))
            .expect("Failed to send response");
    }

    // Respond to a tips request
    pub fn respond_with_tips(
        &mut self,
        channel: ResponseChannel<BeadResponse>,
        tips: Vec<BeadHash>,
    ) {
        self.bead_sync
            .send_response(channel, BeadResponse::Tips(tips))
            .expect("Failed to send response");
    }

    // Respond to a genesis request
    pub fn respond_with_genesis(
        &mut self,
        channel: ResponseChannel<BeadResponse>,
        genesis: Vec<BeadHash>,
    ) {
        self.bead_sync
            .send_response(channel, BeadResponse::Genesis(genesis))
            .expect("Failed to send response");
    }

    // Respond with an error
    pub fn respond_with_error(&mut self, channel: ResponseChannel<BeadResponse>, error: String) {
        self.bead_sync
            .send_response(channel, BeadResponse::Error(error))
            .expect("Failed to send response");
    }
}

#[cfg(test)]
mod tests;
