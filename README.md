
![Build status](https://github.com/wholooks/braidpool/actions/workflows/rust-node.yml/badge.svg)

# Proposal

Read the
[proposal](https://github.com/pool2win/braidpool/raw/main/proposal/proposal.pdf)
for braidpool.

For details on how delivering shares to market makers for enabling hashrate
futures, read the blog post: [Deliver Hashrate to Market
Markets](https://blog.opdup.com/2021/08/18/deliver-hashrate-to-market-makers.html).

The goals of the pool are:

1. Lower variance for independent miners, even when large miners join the pool.
2. Miners build their own blocks, just like in p2pool.
3. Payouts require a constant size blockspace, independent of the number of
   miners on the pool.
4. Provide building blocks for enabling a futures market of hash rates.

# Running the node

Braidpool nodes need to connect to a bitcoin RPC node. Let's assume you are running
one on `0.0.0.0:8332` with username `xxxx` and password `yyyy`.

The bitcoin node also needs to have the `hashblock` [ZMQ notification](https://github.com/bitcoin/bitcoin/blob/master/doc/zmq.md) enabled.
Let's assume this is enabled on port `28332`.

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

The [project on github](https://github.com/wholooks/braidpool/projects/1)
tracks the main components to build. Here's a list to keep us focused:

- [ ] P2P gossip based broadcast of miner blocks and shares.
- [ ] Use FROST rust implementation for providing threshold schnorr
      signatures. Use mock clock for identifying rounds.
- [ ] A DAG of shares to track contributions for miners.
- [ ] Validate received blocks and shares.
- [ ] Single script installer (limited to Linux variants, potentially using
      docker).


Matrix chat: [https://matrix.to/#/#braidpool:matrix.org](https://matrix.to/#/#braidpool:matrix.org)

Mailing list: [https://sourceforge.net/p/braidpool/mailman/braidpool-discuss/](https://sourceforge.net/p/braidpool/mailman/braidpool-discuss/)

Development blog: [https://blog.opdup.com/](https://blog.opdup.com/)

Donations: bitcoin:bc1q6xms5xsq6kvk9h57mvsdxdjnnrl0vsc942xlxe
