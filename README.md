
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

You will need to have `cmake` and `protoc` available on your system to build the node.

For the moment, the node runs a simple p2p broadcast. To run it you need to do
the usual cargo things

```
cd node
cargo build

# run the first seed node on port 8989
cargo run -- --bindport=8989
[2023-10-24T01:26:44Z INFO  braidpool_node] Braidpool node multiaddr: /ip4/127.0.0.1/udp/8989/quic-v1/p2p/12D3KooWBx3CTpqd6N7Hetnz3TYsDUwmPQt9S7wV6Wiw8G47agjT

# run another node while specifying their own port as 9899 and pointing to the seed node
cargo run -- --bindport=9989 --addpeer=/ip4/127.0.0.1/udp/8989/quic-v1/p2p/12D3KooWBx3CTpqd6N7Hetnz3TYsDUwmPQt9S7wV6Wiw8G47agjT
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
