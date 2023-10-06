
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

# Running a mutinynet node

As a strategy to optimize the development workflow, you should use [mutinynet](https://mutinynet.com/) (a modified `signet` with 30s block time). You can
start a local node via
```
cd mutinynet
./run.sh
cd ..
```

The node RPC will be available on `0.0.0.0:38332` with username `braidpooldev` and password `braidpooldev`.

# Running the braidpool node

For the moment, the braidpool node runs a simple p2p broadcast. 
It also connects to a bitcoin RPC node to get new block templates.

To run the braidpool node you need to do the usual cargo things:
```
cd node
cargo build

# run the first seed node on port 8989
cargo run localhost:8989 localhost:8989 

# run other nodes pointing to the seeding node and specify their own port as 9899
cargo run localhost:8989 localhost:9899
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
