
![Build status](https://github.com/wholooks/braidpool/actions/workflows/rust-node.yml/badge.svg)

# Proposal

Read the
[Overview](https://github.com/braidpool/braidpool/blob/master/docs/overview.md)
for [General Considerations for Decentralized Mining Pools](https://github.com/braidpool/braidpool/blob/master/docs/general_considerations.md), or [Braidpool Spec](https://github.com/braidpool/braidpool/blob/master/docs/braidpool_spec.md) in increasing levels of complexity. You may also be interested in our [Roadmap](https://github.com/braidpool/braidpool/blob/master/docs/roadmap.md)

The goals of the pool are:

1. Lower variance for independent miners, even when large miners join the pool.
2. Miners build their own blocks, just like in p2pool.
3. Payouts require a constant size blockspace, independent of the number of
   miners on the pool.
4. Provide building blocks for enabling a futures market of hash rates.

# Running the node

Braidpool nodes need to connect to a bitcoin RPC node. The bitcoin node also needs to have the `hashblock` [ZMQ notification](https://github.com/bitcoin/bitcoin/blob/master/doc/zmq.md) enabled.

Let's assume there is a `bitcoind` running on `0.0.0.0:8332` with username `xxxx`, password `yyyy`, and `zmqpubhashblock` enabled on port `28332`:
```
$ bitcoind -rpcport=8332 -rpcuser=xxxx -rpcpassword=yyyy -zmqpubhashblock=tcp://localhost:28332
```

For the moment, the braidpool node runs a simple p2p broadcast. To run it you need to do
the usual cargo things

```
cd node
cargo build

# run the first seed node on port 8989
cargo run -- --bind=localhost:8989 --bitcoin=0.0.0.0 --rpcport=8332 --rpcuser=xxxx --rpcpass=yyyy --zmqhashblockport=28332

# run other nodes pointing to the seeding node and specify their own port as 9899
cargo run -- --bind=localhost:9899 --addnode=localhost:8989 --bitcoin=0.0.0.0 --rpcport=8332 --rpcuser=xxxx --rpcpass=yyyy --zmqhashblockport=28332
```

# Progress

A list with TODO's:

- [ ] P2P gossip based broadcast of miner blocks and shares.
- [ ] Use FROST rust implementation for providing threshold schnorr
      signatures. Use mock clock for identifying rounds.
- [ ] A DAG of shares to track contributions for miners.
- [ ] Validate received blocks and shares.
- [ ] Single script installer (limited to Linux variants, potentially using
      docker).


[Discord chat](https://discord.gg/pZYUDwkpPv)

