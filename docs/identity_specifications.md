# Miner Identity & Signatures

The core of Braidpool is Bead(s), a replacement for Blocks, and each Bead must be identifiable by the Node/Miner (that submitted them). This is defined using the `CommittedMetadata::comm_pub_key` in the `Bead`, and the Hasher who should receive the payment is the `payout_address`. It's imperative to make sure the PubKey received here is standardized (to avoid accepting different types of PubKeys). 

Every public key committed in a bead must be a BUP340 X-Only secp256k1 key. This ensure that 

- encoding is always 32-bytes
- Compressed (`02`/`03`+ X) is invalid
- Uncompressed (`04` + x + y) is invalid.
- DER encodings are invalid.

This also implies that the `UncommittedMetadata::signature` has to be a BIP340 Schnorr signature over the said key.

> The libp2p swarm key is a different keypair, for now, `ed25519`. It should also be a > BIP340 key. Looking into that step.


## Bead Identity 

### Bead Public Key


|                 | This branch                                                |
| --------------- | ---------------------------------------------------------- |
| Rust type       | `bitcoin::XOnlyPublicKey`                                  |
| Wire            | Exactly 32 raw bytes, no length prefix and no parity byte  |
| JSON / database | Hex of `XOnlyPublicKey::serialize()` (32 bytes)            |
| Curve point     | x-coordinate only. y is the even lift from BIP340 `lift_x` |


`parse_xonly_pubkey` rejects any slice whose length is not 32, and rejects 32 bytes that are not a valid x-coordinate. Consensus decode of `CommittedMetadata` reads 32 bytes and fails the bead on an invalid x-only key.

The secret lives in `datadir/miner_secp256k1` as 32 raw bytes, mode `0o400`, next to the libp2p `keystore`. `MinerIdentity::xonly()` is what every bead from that process commits. `MinerConfig.miner_pubkey` in the TOML config is unused.

### Uncommitted Signature

The signature field must verify under `comm_pub_key` which is what `verify_uncommitted_signature` does. `extend_verified` drops the Bead if the signature is invalid. 


|                 | This branch                                        |
| --------------- | -------------------------------------------------- |
| Rust type       | `bitcoin::secp256k1::schnorr::Signature`           |
| Wire            | Exactly 64 raw bytes, `R (32)                      |
| JSON            | Hex of those 64 bytes                              |
| What was signed | Tagged hash below, with `sign_schnorr_no_aux_rand` |


`sign_bead` sets `comm_pub_key` to this node's x-only key, then signs. Verification uses only the key inside the bead. A signature from another secret, or the same signature copied onto another header or committed payload, fails.

The following paragraph(s) are specifications and are prone to improvements

> The message is a BIP340 tagged hash. The tag is `Braidpool/bead/uncommitted/v1`. The payload, in order, is the consensus encoding of:
> 1. `extra_nonce_1`, `extra_nonce_2` and `broadcast_timestamp`
> 2. The block header
> 3. `CommittedMetadata`, which includes `comm_pub_key`

> The tag and the committed key are inside the signed bytes, so the signature cannot be moved to another bead or checked against a different key type.

The encoding will reject if:

* ECDSA DER public key is detected
* A SIGHASH type byte after the 64 signature bytes
* A 33-byte or 65-byte public key in `comm_pub_key`

## libp2p peer key

| | Current implementation |
| --- | --- |
| Generation | `libp2p::identity::Keypair::generate_ed25519()` |
| Persistence | `to_protobuf_encoding()` / `from_protobuf_encoding()` (libp2p private-key protobuf, not a raw 32-byte secret) |
| Public key | `libp2p::identity::PublicKey::Ed25519`, a 32-byte Ed25519 point |
| Peer id | `PeerId` multihash of that public key. Kademlia, floodsub, and identify all use this id |
| Signature algorithm | Ed25519 (EdDSA on Curve25519). 64 bytes, `R || s`, but not BIP340 |
| Who signs | The swarm, not bead code. QUIC authenticates the peer. Identify (`/braidpool/identify/1.0.0`) publishes `local_key.public()`. Application code never calls `keypair.sign()` |

`getnodeinfo.common_pub_key` is the bead x-only key. `getpeerinfo` is the ed25519 `PeerId`. Those are different identities for the same process.

### Could the swarm key be BIP340 Schnorr

`libp2p` 0.55 has no x-only Schnorr key type. The closest built-in is `Keypair::Secp256k1`, and that is ECDSA: a 33-byte compressed public key and a compact ECDSA signature. Same curve as BIP340, different encoding, different algorithm. `verify_schnorr` will not accept it, and `parse_xonly_pubkey` will not accept the 33-byte key.

A real BIP340 peer identity would leave the stock `identity::Keypair` API.

| | Ed25519 today | Stock libp2p secp256k1 | BIP340 x-only, not supported |
| --- | --- | --- | --- |
| Public key | 32-byte Ed25519 point | 33-byte compressed secp256k1 | 32-byte x-only |
| Signature | 64-byte EdDSA | Compact ECDSA | 64-byte Schnorr `R \|\| s` |
| Keystore | libp2p protobuf | libp2p protobuf | Would need a new protobuf key type |
| `PeerId` | Hash of the Ed25519 public key | Hash of the compressed public key | Would need a new multihash input; every existing peer id would change |
| Handshake | QUIC and identify call `Keypair::sign` | Same, ECDSA | QUIC and identify would need a Schnorr `sign`/`verify` the current crate does not provide |
| Bead check | None. Beads use the other key | Still none. ECDSA does not verify under `comm_pub_key` | Could verify only if the bead signer and the peer key were the same secret |

Keeping the two keys separate matches how miners connect. Many ASICs authorize against one node. Each bead carries that node's x-only key and that worker's payout address. Replacing the swarm key with the miner Schnorr key would tie the gossip `PeerId` to the bead signer: rotating `keystore` would look like a new miner, and the mining identity would be the network address. The bead rule stays BIP340 either way. The peer key stays ed25519 until the libp2p identity stack can carry an x-only key and a Schnorr handshake.