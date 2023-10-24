use futures::StreamExt;

const BEAD_ANNOUNCE_PROTOCOL_NAME: &str = "/notif/bead/1";
const BRAID_SYNC_PROTOCOL_NAME: &str = "/sync/braid/1";
const BRAID_MAX_SIZE: usize = 1024 * 1024;
const BEAD_ANNOUNCE_HANDSHAKE: [u8; 4] = [1, 2, 3, 4];

pub struct P2pEngine {
    bead_announce_handle: litep2p::protocol::notification::NotificationHandle,
    braid_sync_handle: litep2p::protocol::request_response::RequestResponseHandle,
}

impl P2pEngine {
    /// Create new [`P2pEngine`].
    pub fn new() -> (
        Self,
        litep2p::protocol::notification::Config,
        litep2p::protocol::request_response::Config,
    ) {
        let (bead_announce_config, bead_announce_handle) = Self::init_bead_announce();
        let (braid_sync_config, braid_sync_handle) = Self::init_braid_sync();

        (
            Self {
                bead_announce_handle,
                braid_sync_handle,
            },
            bead_announce_config,
            braid_sync_config,
        )
    }

    /// Initialize notification protocol for bead announcements
    fn init_bead_announce() -> (
        litep2p::protocol::notification::Config,
        litep2p::protocol::notification::NotificationHandle,
    ) {
        litep2p::protocol::notification::ConfigBuilder::new(
            litep2p::types::protocol::ProtocolName::from(BEAD_ANNOUNCE_PROTOCOL_NAME),
        )
        .with_max_size(1024usize)
        .with_handshake(BEAD_ANNOUNCE_HANDSHAKE.to_vec())
        .build()
    }

    /// Initialize request-response protocol for braid syncing.
    fn init_braid_sync() -> (
        litep2p::protocol::request_response::Config,
        litep2p::protocol::request_response::RequestResponseHandle,
    ) {
        litep2p::protocol::request_response::ConfigBuilder::new(
            litep2p::types::protocol::ProtocolName::from(BRAID_SYNC_PROTOCOL_NAME),
        )
        .with_max_size(BRAID_MAX_SIZE)
        .build()
    }

    /// Start event loop for [`P2pEngine`].
    pub async fn run(mut self) {
        loop {
            tokio::select! {
                _ = self.bead_announce_handle.next() => todo!(),
                _ = self.braid_sync_handle.next() => todo!()
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::p2p::*;
    use crate::*;

    #[tokio::test]
    async fn bead_announce_works() {
        // setup alice
        let (mut engine_alice, bead_announce_config_alice, _) = p2p::P2pEngine::new();
        let config_alice = litep2p::config::Litep2pConfigBuilder::new()
            .with_quic(litep2p::transport::quic::config::TransportConfig {
                listen_address: "/ip4/127.0.0.1/udp/0/quic-v1".parse().unwrap(),
            })
            .with_notification_protocol(bead_announce_config_alice)
            .build();
        let mut litep2p_alice = litep2p::Litep2p::new(config_alice).await.unwrap();
        let peerid_alice = *litep2p_alice.local_peer_id();

        // setup bob
        let (mut engine_bob, bead_announce_config_bob, _) = p2p::P2pEngine::new();
        let config_bob = litep2p::config::Litep2pConfigBuilder::new()
            .with_quic(litep2p::transport::quic::config::TransportConfig {
                listen_address: "/ip4/127.0.0.1/udp/0/quic-v1".parse().unwrap(),
            })
            .with_notification_protocol(bead_announce_config_bob)
            .build();
        let mut litep2p_bob = litep2p::Litep2p::new(config_bob).await.unwrap();
        let peerid_bob = *litep2p_bob.local_peer_id();

        // alice listens
        let listen_address_alice = litep2p_alice.listen_addresses().next().unwrap().clone();

        // bob dials
        litep2p_bob
            .dial_address(listen_address_alice)
            .await
            .unwrap();

        // spawn event listeners
        let (res1, res2) = tokio::join!(litep2p_alice.next_event(), litep2p_bob.next_event());

        // assert connections established
        assert!(std::matches!(
            res1,
            Some(litep2p::Litep2pEvent::ConnectionEstablished { .. })
        ));
        assert!(std::matches!(
            res2,
            Some(litep2p::Litep2pEvent::ConnectionEstablished { .. })
        ));

        engine_alice
            .bead_announce_handle
            .open_substream(peerid_bob)
            .await
            .unwrap();
        engine_bob
            .bead_announce_handle
            .open_substream(peerid_alice)
            .await
            .unwrap();

        assert_eq!(
            engine_alice.bead_announce_handle.next().await.unwrap(),
            litep2p::protocol::notification::NotificationEvent::ValidateSubstream {
                protocol: litep2p::types::protocol::ProtocolName::from(BEAD_ANNOUNCE_PROTOCOL_NAME),
                fallback: None,
                peer: peerid_bob,
                handshake: BEAD_ANNOUNCE_HANDSHAKE.to_vec(),
            }
        );
        engine_alice
            .bead_announce_handle
            .send_validation_result(
                peerid_bob,
                litep2p::protocol::notification::ValidationResult::Accept,
            )
            .await;

        // accept the substreams
        assert_eq!(
            engine_bob.bead_announce_handle.next().await.unwrap(),
            litep2p::protocol::notification::NotificationEvent::ValidateSubstream {
                protocol: litep2p::types::protocol::ProtocolName::from(BEAD_ANNOUNCE_PROTOCOL_NAME),
                fallback: None,
                peer: peerid_alice,
                handshake: BEAD_ANNOUNCE_HANDSHAKE.to_vec(),
            }
        );
        engine_bob
            .bead_announce_handle
            .send_validation_result(
                peerid_alice,
                litep2p::protocol::notification::ValidationResult::Accept,
            )
            .await;

        assert_eq!(
            engine_bob.bead_announce_handle.next().await.unwrap(),
            litep2p::protocol::notification::NotificationEvent::NotificationStreamOpened {
                protocol: litep2p::types::protocol::ProtocolName::from(BEAD_ANNOUNCE_PROTOCOL_NAME),
                fallback: None,
                peer: peerid_alice,
                handshake: BEAD_ANNOUNCE_HANDSHAKE.to_vec(),
            }
        );
        assert_eq!(
            engine_alice.bead_announce_handle.next().await.unwrap(),
            litep2p::protocol::notification::NotificationEvent::NotificationStreamOpened {
                protocol: litep2p::types::protocol::ProtocolName::from(BEAD_ANNOUNCE_PROTOCOL_NAME),
                fallback: None,
                peer: peerid_bob,
                handshake: BEAD_ANNOUNCE_HANDSHAKE.to_vec(),
            }
        );

        const ALICE_BEAD_ANNOUNCE: [u8; 4] = [1, 3, 3, 7];
        const BOB_BEAD_ANNOUNCE: [u8; 4] = [1, 3, 3, 8];

        engine_alice
            .bead_announce_handle
            .send_sync_notification(peerid_bob, ALICE_BEAD_ANNOUNCE.to_vec())
            .unwrap();
        engine_bob
            .bead_announce_handle
            .send_sync_notification(peerid_alice, BOB_BEAD_ANNOUNCE.to_vec())
            .unwrap();

        assert_eq!(
            engine_bob.bead_announce_handle.next().await.unwrap(),
            litep2p::protocol::notification::NotificationEvent::NotificationReceived {
                peer: peerid_alice,
                notification: ALICE_BEAD_ANNOUNCE.to_vec(),
            }
        );
        assert_eq!(
            engine_alice.bead_announce_handle.next().await.unwrap(),
            litep2p::protocol::notification::NotificationEvent::NotificationReceived {
                peer: peerid_bob,
                notification: BOB_BEAD_ANNOUNCE.to_vec(),
            }
        );
    }

    #[tokio::test]
    async fn braid_sync_works() {
        // setup alice
        let (mut engine_alice, _, braid_sync_config_alice) = p2p::P2pEngine::new();
        let config_alice = litep2p::config::Litep2pConfigBuilder::new()
            .with_quic(litep2p::transport::quic::config::TransportConfig {
                listen_address: "/ip4/127.0.0.1/udp/0/quic-v1".parse().unwrap(),
            })
            .with_request_response_protocol(braid_sync_config_alice)
            .build();
        let mut litep2p_alice = litep2p::Litep2p::new(config_alice).await.unwrap();
        let peerid_alice = *litep2p_alice.local_peer_id();

        // setup bob
        let (mut engine_bob, _, braid_sync_config_bob) = p2p::P2pEngine::new();
        let config_bob = litep2p::config::Litep2pConfigBuilder::new()
            .with_quic(litep2p::transport::quic::config::TransportConfig {
                listen_address: "/ip4/127.0.0.1/udp/0/quic-v1".parse().unwrap(),
            })
            .with_request_response_protocol(braid_sync_config_bob)
            .build();
        let mut litep2p_bob = litep2p::Litep2p::new(config_bob).await.unwrap();
        let peerid_bob = *litep2p_bob.local_peer_id();

        // alice listens
        let listen_address_alice = litep2p_alice.listen_addresses().next().unwrap().clone();

        // bob dials
        litep2p_bob
            .dial_address(listen_address_alice)
            .await
            .unwrap();

        // spawn event listeners
        let (res1, res2) = tokio::join!(litep2p_alice.next_event(), litep2p_bob.next_event());

        assert!(std::matches!(
            res1,
            Some(litep2p::Litep2pEvent::ConnectionEstablished { .. })
        ));
        assert!(std::matches!(
            res2,
            Some(litep2p::Litep2pEvent::ConnectionEstablished { .. })
        ));

        const ALICE_BRAID_SYNC_REQ: [u8; 4] = [1, 3, 3, 7];

        // send request to remote peer
        let request_id = engine_alice
            .braid_sync_handle
            .send_request(
                peerid_bob,
                ALICE_BRAID_SYNC_REQ.to_vec(),
                litep2p::protocol::request_response::DialOptions::Reject,
            )
            .await
            .unwrap();
        assert_eq!(
            engine_bob.braid_sync_handle.next().await.unwrap(),
            litep2p::protocol::request_response::RequestResponseEvent::RequestReceived {
                peer: peerid_alice,
                fallback: None,
                request_id,
                request: ALICE_BRAID_SYNC_REQ.to_vec(),
            }
        );

        const BOB_BRAID_SYNC_RES: [u8; 4] = [1, 3, 3, 8];

        // send response to the received request
        engine_bob
            .braid_sync_handle
            .send_response(request_id, BOB_BRAID_SYNC_RES.to_vec())
            .await
            .unwrap();
        assert_eq!(
            engine_alice.braid_sync_handle.next().await.unwrap(),
            litep2p::protocol::request_response::RequestResponseEvent::ResponseReceived {
                peer: peerid_bob,
                request_id,
                response: BOB_BRAID_SYNC_RES.to_vec(),
            }
        );
    }
}
