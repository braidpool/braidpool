# Miner Identity & Signatures

Miners on Braidpool are only identified by their public keys which they provide to braidpool inside each `Bead` as part of the `CommittedMetadata::comm_pub_key`. They also provide their public key when encrypting messages across libp2p (ECIES is on the roadmap). We do not want to allow arbitrary public key(s) to be provided, as is possible on Bitcoin. Instead, Braidpool allows miners to specify their _Schnorr-compatible_ `XOnlyPublicKey` as the `comm_pub_key`. This then dictates that the `UnCommittedMetadata::signature` will also be `Schnorr-based`.

The libp2p signs its own connection handshake with ECDSA, using the same (miner) key. See [Why the transport signature is ECDSA](#why-the-transport-signature-is-ecdsa).

# Specification

## Bead public key

|                 |                                                                                           |
| --------------- | ----------------------------------------------------------------------------------------- |
| Rust type       | `bitcoin::XOnlyPublicKey`                                                                 |
| Wire            | 32 bytes                               |
| JSON / database | `XOnlyPublicKey::serialize()` (hex)                          |
| Curve point     | the x-coordinate only. The y-coordinate is the **even-y** lift defined by BIP340 `lift_x` |

Rejected, and the bead is invalid: anything other than a BIP-340 compatible public key.

## Bead signature

|                 |                                                                                                                                                                                                                       |
| --------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Rust type       | `bitcoin::secp256k1::schnorr::Signature`                                                                                                                                                                              |
| Wire            | 64 bytes: `R.x` (32 bytes) + `s` (32 bytes)                                                                                                                                                    |
| JSON / database | lowercase hex of those 64 bytes (128 hex chars)                                                                                                                                                                       |
| Scheme          | BIP340 |

## Message (what is signed)

```
digest  = tagged_hash("Braidpool/bead/uncommitted/v1", payload)
tagged_hash(tag, m) = SHA256( SHA256(tag) || SHA256(tag) || m )      (BIP340)
payload = extra_nonce_1                  u64, little-endian, 8 bytes
       || extra_nonce_2                  u64, little-endian, 8 bytes
       || broadcast_timestamp            u32, little-endian, 4 bytes (consensus value)
       || block_header                   80 bytes, Bitcoin consensus encoding
       || committed_metadata             Braidpool consensus encoding (includes comm_pub_key)
```

The signature field is excluded from what is signed. Because the header and the committed metadata, including `comm_pub_key`, are inside the signed bytes, a valid signature cannot be moved onto a different bead, and changing any signed field, invalidates it.

> This does not stop someone from replacing the signature as a whole because that involves that the proof of work does not yet commit to the committed metadata, so anyone who relays a bead can put their own key in `comm_pub_key` (and their own `payout_address`), re-sign, and the same proof of work verifies under their key. A valid signature proves only that the holder of `comm_pub_key` signed this exact bead, not that they mined it. 

## Miner key file

The secret behind `comm_pub_key` is stored at `datadir/`.

|            |                                                                             |
| ---------- | --------------------------------------------------------------------------- |
| Content    | exactly 32 raw bytes: the secret scalar, big-endian                         |
| Mode       | `0o400` (owner read-only), on Unix                                          |
| Created by | `MinerIdentity::load_or_generate`, via `secret_file::read_or_create_secret` |

**Creation is atomic.** A new key is written to a temporary sibling that is created with
mode `0o400` from the first instant, flushed to disk, and then published under its final
name with a hard link, which fails if the name already exists. This means:

- the secret never exists on disk with wider permissions
- the final name never holds a partial file
- two processes starting at once on the same datadir end up with the same key: one
creates it, the other reads it. No process can overwrite another's key.

If the filesystem does not support hard links, the file is written directly with
`create_new` and the same mode, which still never overwrites.

## libp2p peer key

We keep one shared secret for a node and the libp2p derives its `PeerId` from it. This same key generates the `comm_pub_key`.

|                      |                                                                                                                                                                 |
| -------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------------                                                                                           |
| Public key           | 33-byte compressed secp256k1 point, always the even-y form (`02` followed by x) |
| `PeerId`             | identity multihash of the encoded public key (`16Uiu2HA…`) |
| Transport signatures | **ECDSA** This is libp2p's secp256k1 scheme |                     

- The x-coordinate of the libp2p public key **is** the bead `comm_pub_key`.
- The secret is normalised to its even-y form before the libp2p key is built. 
- Any peer can read the miner key out of a secp256k1 `PeerId` and compare it with a  bead's `comm_pub_key`.
- One secret per machine. Running the same secret on two machines yields the same  
`PeerId`. Two nodes on one machine need separate  
data directories.

## Why the transport signature is ECDSA

libp2p picks the signature scheme from the key type. For secp256k1 that is ECDSA, and there is no BIP340 key type. Using Schnorr in the handshake would mean adding one: a fork of `libp2p-identity` and `libp2p-tls` kept in step with every libp2p release, and `PeerId`s that standard libp2p tools cannot read. The benefit is small, because the signature only proves the peer holds the key, and it is the same key that signs the peer's  beads.
