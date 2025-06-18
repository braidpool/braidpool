use std::{error::Error, time::Duration};

use libp2p::{
    identify,
    identity::Keypair,
    kad::{self, store::MemoryStore},
    ping,
    swarm::NetworkBehaviour,
    StreamProtocol,
};

#[derive(NetworkBehaviour)]
//Custom behaviour for braidpool
pub struct BraidPoolBehaviour {
    pub kademlia: kad::Behaviour<MemoryStore>,
    pub identify: identify::Behaviour,
    pub ping: ping::Behaviour,
}

pub const KADPROTOCOLNAME: StreamProtocol = StreamProtocol::new("/braidpool/kad/1.0.0");
pub const IDENTIFYPROTOCOLNAME: StreamProtocol = StreamProtocol::new("/braidpool/identify/1.0.0");
impl BraidPoolBehaviour {
    pub fn new(local_key: &Keypair) -> Result<BraidPoolBehaviour, Box<dyn Error>> {
        //initializing the store for kademlia based DHT
        let store = MemoryStore::new(local_key.public().to_peer_id());
        //custom kademlia protocol
        let mut kad_config = kad::Config::new(KADPROTOCOLNAME);
        kad_config.set_query_timeout(tokio::time::Duration::from_secs(60));
        //custom kad configuration
        let kademlia_behaviour =
            kad::Behaviour::with_config(local_key.public().to_peer_id(), store, kad_config);
        //identify protocol configuration
        let identify_config =
            identify::Config::new(IDENTIFYPROTOCOLNAME.to_string(), local_key.public());
        let identify_behaviour = identify::Behaviour::new(identify_config);
        let ping_config = ping::Config::default()
            .with_timeout(Duration::from_secs(3600))
            .with_interval(Duration::from_millis(1));
        let ping_behaviour = ping::Behaviour::new(ping_config.clone());
        let braidpool_behaviour = BraidPoolBehaviour {
            identify: identify_behaviour,
            ping: ping_behaviour,
            kademlia: kademlia_behaviour,
        };

        return Ok(braidpool_behaviour);
    }
}
