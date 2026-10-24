# Miner Identity & Signatures

Beads replace blocks, and every bead must be attributable to the node that produced it.
That attribution is `CommittedMetadata::comm_pub_key`, and the bead is authenticated by
`UnCommittedMetadata::signature`. The party that is paid is identified separately, by `payout_address`.

**Rule.** Braidpool supports exactly one public-key format and exactly one signature
scheme for anything it defines itself:

- public keys are **BIP340 x-only secp256k1 keys**, 32 bytes;
- signatures are **BIP340 Schnorr signatures**, 64 bytes.

No other encoding, curve, hash-type byte or signature scheme is accepted, even for
compatibility. This avoids the variation Bitcoin tolerates (compressed, uncompressed,
DER, ECDSA, sighash suffixes).

There is one place where a different signature scheme appears, and it is not Braidpool's:
libp2p signs its own connection handshake with ECDSA, using the same key. See
[Why the transport signature is ECDSA](#why-the-transport-signature-is-ecdsa).

**How this document is organised.**


| Part                                                                 | Contents                                                                |
| -------------------------------------------------------------------- | ----------------------------------------------------------------------- |
| [Specification](#specification)                                      | key format, signature, key file, libp2p identity, protocol 2.0.0        |
| [After you pull this change](#after-you-pull-this-change-developers) | what breaks on a developer machine and what to do                       |
| [Questions for review](#questions-for-the-cryptographer-review)      | each open question in plain terms, and what happens if the answer is no |
| [ECIES](#ecies-between-mining-nodes)                                 | design notes for encrypted messaging between miners (not implemented)   |


---

# Specification

## Bead public key


|                 |                                                                                           |
| --------------- | ----------------------------------------------------------------------------------------- |
| Rust type       | `bitcoin::XOnlyPublicKey`                                                                 |
| Wire            | exactly 32 raw bytes, no length prefix and no parity byte                                 |
| JSON / database | lowercase hex of `XOnlyPublicKey::serialize()` (64 hex chars)                             |
| Curve point     | the x-coordinate only. The y-coordinate is the **even-y** lift defined by BIP340 `lift_x` |


Rejected, and the bead is invalid: a 33-byte compressed key (`02`/`03` + x), a 65-byte
uncompressed key (`04` + x + y), any DER-encoded key, any 32 bytes that are not a valid
x-coordinate on the curve. `parse_xonly_pubkey` enforces this for the database and RPC
paths, and `CommittedMetadata` decoding enforces it on the wire.

## Bead signature


|                 |                                                                                                                                                                                                           |
| --------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Rust type       | `bitcoin::secp256k1::schnorr::Signature`                                                                                                                                                                  |
| Wire            | exactly 64 raw bytes, `R.x (32)                                                                                                                                                                           |
| JSON / database | lowercase hex of those 64 bytes (128 hex chars)                                                                                                                                                           |
| Scheme          | BIP340, deterministic (`sign_schnorr_no_aux_rand`): no auxiliary randomness, the nonce is derived from the secret, the public key and the message, so the same bead signed twice gives the same signature |


### Message

```
digest  = tagged_hash("Braidpool/bead/uncommitted/v1", payload)
tagged_hash(tag, m) = SHA256( SHA256(tag) || SHA256(tag) || m )      (BIP340)
payload = extra_nonce_1                  u64, little-endian, 8 bytes
       || extra_nonce_2                  u64, little-endian, 8 bytes
       || broadcast_timestamp            u32, little-endian, 4 bytes (consensus value)
       || block_header                   80 bytes, Bitcoin consensus encoding
       || committed_metadata             Braidpool consensus encoding (includes comm_pub_key)
```

Only the signature field is excluded from what is signed. Because the header and the
committed metadata, including `comm_pub_key`, are inside the signed bytes, a valid
signature cannot be moved onto a different bead, and cannot be checked against a
different key.

### Signing

`MinerIdentity::sign_bead` first sets `comm_pub_key` to the node's x-only key, then
signs the digest. Implementations must not hand-adjust the secret for odd-y public
keys: the BIP340 signing routine already negates the secret internally when the public
point has odd y.

### Verification

`verify_uncommitted_signature` recomputes the digest and verifies the 64-byte signature
against the `comm_pub_key` carried in the same bead. No other key is consulted.
`extend_verified` rejects a bead with an invalid signature before `Braid::extend` on
every ingestion path (gossip, initial sync, RPC `addbead`, database reload, audit DAG).
Locally formed beads are signed by the node itself immediately before insertion.

Rejected, and the bead is invalid: a signature that is not exactly 64 bytes, an ECDSA
DER signature, a trailing sighash-type byte, and any signature that does not verify.

### Signature tags

Every signed object type has its own tag so that a signature made for one can never be
valid for another. Convention: `Braidpool/<object>/<purpose>/v<N>`. The tag names are proposals up for review; the rule that matters is that no two object types share a tag.


| Tag                             | Signed object                          | Status      |
| ------------------------------- | -------------------------------------- | ----------- |
| `Braidpool/bead/uncommitted/v1` | bead authentication (above)            | Implemented |
| `Braidpool/ecies/...`           | any future signed ECIES handshake data | Reserved    |


A tag for binding a PeerId to the miner key was considered and is **not needed**: the
libp2p key is derived from the miner secret, so the link is structural (see below).

## Miner key file

The secret behind `comm_pub_key` is stored at `datadir/miner_secp256k1`.


|            |                                                                             |
| ---------- | --------------------------------------------------------------------------- |
| Content    | exactly 32 raw bytes: the secret scalar, big-endian                         |
| Mode       | `0o400` (owner read-only), on Unix                                          |
| Created by | `MinerIdentity::load_or_generate`, via `secret_file::read_or_create_secret` |


**Why `0o400`.** Anyone who can read this file can forge beads as this miner. The file
is owner-read-only so no other local user can read it, and no process (including this
one) can modify it by accident.

**Creation is atomic.** A new key is written to a temporary sibling that is created with
mode `0o400` from the first instant, flushed to disk, and then published under its final
name with a hard link, which fails if the name already exists. Consequences:

- the secret never exists on disk with wider permissions
- the final name never holds a partial file
- two processes starting at once on the same datadir end up with the same key: one
creates it, the other reads it. No process can overwrite another's key.

If the filesystem does not support hard links, the file is written directly with
`create_new` and the same mode, which still never overwrites.

**Loading rules.**

- Only a missing file (`NotFound`) causes a key to be generated.
- Any other read error aborts startup. An identity is never regenerated over a path
that could not be read.
- The path must be a regular file. A directory or other object there is an error.
- The content must be exactly 32 bytes and a valid, non-zero scalar below the curve
order. Anything else is an error and the file is left untouched.
- A file whose mode is not `0o400` is tightened to `0o400` and a warning is logged.

## Denied keys

Some keys have publicly known secrets, so anyone can sign as them. They are refused: a
bead whose `comm_pub_key` is on the denylist is rejected even if its signature is valid
(`extend_verified`, so on every ingestion path), and a node refuses to start with such a
miner key. This is a validation policy, not part of the encoding, so changing the list
never changes the wire format.

The default list is computed from secrets, never hard-coded as public keys. It has 1,027
entries in two groups. A secret and its negation share one x-only key, so negating a known
secret does not escape the list.

| Group | Secrets | Keys |
| --- | --- | --- |
| Small secrets | `1` to `1024` | the x-only key of `k * G` for each `k`: 1,024 keys |
| BIP340 test vectors | the three secret keys published with the BIP340 test vectors (vector 0, secret `3`, is already in the group above) | 3 keys |

| Secret | Denied x-only key |
| --- | --- |
| `1` (the generator point G) | `79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798` |
| `2` | `c6047f9441ed7d6d3045406e95c07cd85c778e4b8cef3ca7abac09b95c709ee5` |
| `3` | `f9308a019258c31049344f85f89d5229b531c845836f99b08601f113bce036f9` |
| BIP340 vector 1 | `dff1d77f2a671c5f36183726db2341be58feae1da2deced843240f7b502ba659` |
| BIP340 vector 2 | `dd308afec5777e13121fa72b9cc1b7cc0139715309b086c960e18fd969774eb8` |
| BIP340 vector 3 | `25d1dff95105f5253c4022f628a996ad3a0d95fbf21d468a1b33f8c160d8f517` |

Operators can extend the list, or drop the built-in part:

- `--deny-key <64 hex>` adds a key; repeat it for more. Anything that is not exactly a
  32-byte x-only key stops startup.
- `--no-default-key-denylist` drops the built-in groups (for local experiments only); keys
  given with `--deny-key` still apply.

The list is installed once at startup. It is empty in unit tests, so test fixtures that use
secret 1 keep working.

The list applies to beads and to the node's own key. It is not part of the peer policy: a peer
whose `PeerId` carries a denied key can still connect, and any bead it signs itself is
rejected, while beads it merely relays are judged by their own authors' keys.

## libp2p peer key

There is one secret per node, `datadir/miner_secp256k1`. The libp2p key is derived from it
by `MinerIdentity::libp2p_keypair`, so the node's `PeerId` and the `comm_pub_key` in every
bead it forms come from the same key.


|                      |                                                                                                                                                                 |
| -------------------- | --------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| Derivation           | the 32-byte miner secret loaded as a libp2p `secp256k1::SecretKey`                                                                                              |
| Public key           | 33-byte compressed secp256k1 point, always the even-y form (`02` followed by x): libp2p's encoding of the same point whose x-coordinate is the 32-byte bead key |
| `PeerId`             | identity multihash of the encoded public key (`16Uiu2HA…`); it contains the key                                                                                 |
| Transport signatures | **ECDSA** (SHA-256, DER), made by libp2p once per connection during the handshake. This is libp2p's secp256k1 scheme; it is not BIP340                          |
| Used by              | Kademlia, floodsub, identify and the QUIC/TLS handshake                                                                                                         |
| Retired              | `datadir/keystore` (random ed25519). It is no longer read or written. If present, the node logs a warning and ignores it; it is not deleted                     |


What is shared is the key, not the signature scheme. The 32-byte bead key and the 33-byte
libp2p key are two encodings of one point, so there is no second key and no conflict with
the "x-only only" rule: that rule governs the fields Braidpool defines, and the 33-byte
form appears only inside libp2p's own `PeerId` and handshake.

- The x-coordinate of the libp2p public key (`bytes[1..33]` of the 33-byte form) **is**
the bead `comm_pub_key`.
- The secret is normalised to its even-y form before the libp2p key is built. A secret `d`
and its negation `n - d` have the same x-only key but opposite parity, so without this one
bead key could run as two different `PeerId`s. After normalising, the libp2p public key
always starts with `02` and a bead key corresponds to exactly one `PeerId`. BIP340 signing
is unaffected, because it normalises internally. `xonly_from_public_key` accepts only the
`02` form, so a hand-built `03` key carries no miner key and is ignored by the key policy.
- Any peer can read the miner key out of a secp256k1 `PeerId` and compare it with a
bead's `comm_pub_key`. No additional signature is needed. The helpers are
`miner_identity::xonly_from_public_key`, `xonly_from_peer_id` and `peer_id_matches_xonly`.
- Braidpool-defined signatures (beads and anything added later) are always BIP340
Schnorr. "Schnorr only" applies to what Braidpool defines; the handshake is libp2p's.
- One secret per machine. Running the same secret on two machines yields the same  
`PeerId`, which the network treats as one node. Two nodes on one machine need separate  
data directories.

### Why the transport signature is ECDSA

**What it signs.** When two nodes connect over QUIC, libp2p runs a TLS handshake. Each side
creates a throwaway TLS certificate and signs the string `libp2p-tls-handshake:` followed by
that certificate's public key, using its host key, so the other side learns that the
certificate belongs to that `PeerId`. That is the only signature the host key makes: once
per connection, by libp2p, before any Braidpool code runs. It is **not** made over gossip
messages, bead-sync requests or identify messages (floodsub does not sign messages at all).
The beads inside those messages carry their own Schnorr signatures, made by Braidpool, and
that is what makes a bead valid no matter which peer relayed it.

**Why not BIP340 there.** libp2p picks the signature scheme from the key type. For
secp256k1 that is ECDSA, and there is no BIP340 key type. Using Schnorr in the handshake
would mean adding one: a fork of `libp2p-identity` and `libp2p-tls` kept in step with every
libp2p release, and `PeerId`s that standard libp2p tools cannot read. The benefit is small,
because the signature only proves the peer holds the key, and it is the same key that signs
the peer's beads.

**If Schnorr end to end is wanted.** Keep a throwaway libp2p transport key and have peers
prove their miner key with a Schnorr signature in a Braidpool handshake message (tag
`Braidpool/peer-binding/v1`). The `PeerId` would then no longer carry the miner key.

### Peer policy

libp2p accepts an ed25519 peer on a secp256k1 node, so the restriction to secp256k1
identities is enforced by Braidpool.

- **Key policy** (`--require-secp256k1-peers`, **on by default**; `=false` turns it
off). A peer whose `PeerId` does not carry a miner key is ignored (see quarantine
below) from the moment the connection is established (`peer_meets_key_policy`).
- The `PeerId` is enough. The transport handshake proves the remote controls the key
behind its `PeerId`, and a secp256k1 `PeerId` contains that key, so no identify
payload is trusted and there is nothing for a peer to forge.
- **Version policy.** A peer whose identify `protocol_version` is not ours is ignored as
soon as it identifies itself (`is_current_protocol_version`). This policy has no
switch: such a peer cannot decode our beads.
- `getpeerinfo` reports each peer's `bead_key` (hex x-only key), or `null` for a peer
without a miner key.
- Beads are **not** rejected based on the peer that delivered them: floodsub relays
beads, so the sender is often not the author. A bead is valid or not by its own
signature.

**Quarantine, not disconnect.** An ignored peer is left connected but unused: it is not
added to the peer manager, to floodsub's partial view or to the DHT, and it is logged
once. Disconnecting is worse. A disconnected floodsub peer redials immediately, and in a
test with a peer on another protocol version that was **2,252 reconnects in 6 seconds and
about 220% CPU on the rejecting node** (debug build, same machine); quarantining the same
peer used about **0.1% CPU**. The protocols themselves do not negotiate with an
incompatible peer, so an idle connection cannot exchange beads.

## Protocol 2.0.0

The `Bead` wire encoding changed in this release: 32-byte x-only keys and 64-byte
Schnorr signatures replace 33-byte compressed keys and DER signatures. Nodes on
different versions cannot exchange beads, so the network is cut over as a whole.

**Why "2.0.0".** The previous names ended in `1.0.0`, and the encoding changed in a way old
nodes cannot read, so the number goes up. It makes no stability promise. It exists so
that old and new test nodes ignore each other instead of connecting and then failing to
decode. Nothing outside the core developers runs this network yet.


| Name         | Value                        | How it separates old from new                                                                                                                    |
| ------------ | ---------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------ |
| Kademlia     | `/braidpool/kad/2.0.0`       | a real stream protocol: peers on another version fail to negotiate, so the DHTs stay apart                                                       |
| Bead sync    | `/braidpool/bead-sync/2.0.0` | a real stream protocol: requests to an old peer fail as unsupported                                                                              |
| Gossip topic | `braidpool_channel/2.0.0`    | floodsub's own name (`/floodsub/1.0.0`) is fixed by libp2p and cannot carry a version, so the topic carries it; old and new peers share no topic |
| Identify     | `/braidpool/identify/2.0.0`  | only the `protocol_version` string inside identify messages. Nothing checks it by itself; the version policy above does                          |


A test pins every name to `PROTOCOL_VERSION`, and another that a peer identifying with
the old string fails the check.

**Database format version.** The SQLite databases carry `PRAGMA user_version = 2`.

- A new database is stamped with 2.
- A database with version 0 (created before versioning) that holds beads cannot be
read: its rows have 33-byte keys and DER signatures. The node stops at startup with an
error that says what to delete, instead of failing later with a decode error on the
first row.
- A version-0 database with no beads is stamped in place.
- A database with a higher version than the node knows is refused.

---

# After you pull this change (developers)

The network is a testnet run by the core developers, so there is no staged migration:
everyone moves together. What changes on your machine:

1. **Old databases.** If `braidpool.db` holds beads from before this change, the node
  refuses to start and names the file. Delete `braidpool.db`, `braidpool.db-wal` and
   `braidpool.db-shm` (and `audit.db*` in audit mode) and start again. The braid is
   rebuilt from peers. Nothing else in the datadir needs to go.
2. **Your miner key is kept.** `datadir/miner_secp256k1` is reused if it exists and
  created (owner read-only) if not.
3. **Your `PeerId` changes**, because it now comes from the miner key. If you wrote a
  `/p2p/<PeerId>` into an `--addnode` or a script, update it; addresses without a
   `PeerId` are unaffected. `datadir/keystore` is ignored and can be deleted.
4. **Old and new nodes ignore each other.** They may stay connected but exchange
  nothing, and the log says "Ignoring peer" once per peer. If your node sees no peers,
   check the other side is on this version too.
5. **No bootnode yet.** The hard-coded bootnode still runs the old version, so a fresh
  node finds no one by itself. Connect nodes with
   `--addnode=/ip4/<host>/udp/<port>/quic-v1`. There is a TODO in `main.rs` until the
   bootnode is upgraded.
6. **Two nodes on one machine need separate datadirs.** Same key, same `PeerId`.
7. **No going back.** A datadir this version has created is stamped with database version
  2; to run an older build again, delete the database.
8. **Test keys are refused.** A node whose `miner_secp256k1` holds a publicly known secret
   (for example secret 1, the generator point) stops at startup with a message naming the
   key; delete the file to get a fresh key. `--no-default-key-denylist` turns the built-in
   list off for local experiments.
9. **Flag.** `--require-secp256k1-peers` is on by default. `=false` only lets in peers
  without a miner key; peers on another protocol version are ignored regardless.

---

# Questions for the Cryptographer review

Each question is stated for the reviewer, then in plain terms: what it really asks, and
what changes if the answer is no.

**Q1. One secret under ECDSA (libp2p) and BIP340 Schnorr (beads).**
The libp2p secp256k1 key is the miner secret. libp2p signs with ECDSA (RFC 6979
deterministic nonce, SHA-256, DER) via `k256`; beads sign with BIP340 via `libsecp256k1`.
One private key is used by two different signature systems. Neither standard has been proven
safe when its key is also used by the other, and nobody knows an attack. We believe it is
fine because the two never sign the same kind of data, and nobody can get an ECDSA
signature on a message of their choosing from this key: the only ECDSA signature is libp2p's
connection handshake, over a certificate key the node generates itself. Beads are
Schnorr-signed, by the node that creates them, over fields that connected miners partly
choose (nonce, extranonce, time, payout address); BIP340 is designed for that, because its
security assumes the attacker chooses the messages.

**Q2. Deterministic BIP340 signing.** Beads are signed with `sign_schnorr_no_aux_rand`, so a signature is a pure function of the key and the bead. That helps reproducibility and testing. BIP340 recommends fresh auxiliary randomness as hardening against fault and side-channel attacks. Should we stick to random auxiliary or not?

**Q3. Is the signed bead payload unambiguous?** The payload concatenates fixed-width fields with `committed_metadata`, whose `TxIdVec`,
parents, timestamps and strings are length-prefixed by consensus encoding.

**Q4. Is the key bound to the proof of work?** The signature authenticates the signer, but it does not by itself bind the signer to the work. In audit mode `compute_audit_bead_hash` covers the header and the committed metadata
(and so the key). In normal mode the coinbase OP_RETURN carries only a short commitment,
and no check ties the full committed metadata, including `comm_pub_key` and
`payout_address`, to the header. This is important question for payouts.

**Decided in code, for the reviewer to confirm.** Three questions that were open earlier are
now settled in the implementation; please check the reasoning in the linked sections.

- One bead key is exactly one `PeerId`: the libp2p key is derived from the even-y form of the
  secret (see [libp2p peer key](#libp2p-peer-key)).
- ECDH never guesses the parity of an x-only key: every static and ephemeral key is
  normalised (see [ECIES](#ecies-between-mining-nodes)).
- Keys whose secrets are public are refused (see [Denied keys](#denied-keys)).

---

## ECIES between mining nodes

Purpose (from `general_considerations.md`): keys "necessary for encrypted communication with this miner" and out-of-band contact information, for example coordination of payout signing. The specification says encrypted miner communication builds on StratumV2, which may already cover part of it. This stays a proof of concept.

Key handling is settled: use `canonical_secret()` (the even-y form of a secret) for every
static and ephemeral key, send ephemeral public keys as 32-byte x-only keys, and compute the
shared point with `ecdh_shared_point`, which multiplies the canonical secret by the peer's
even-y lifted key so both sides get the identical point. Without this, about half of all
pairs derive different keys (1,005 of 2,000 in a test). The KDF stays the caller's, with its
own domain-separated tag (`Braidpool/ecies/...`).
