
![Build status](https://github.com/wholooks/braidpool/actions/workflows/cmake.yml/badge.svg)

# Proposal

Read the
[proposal](https://github.com/pool2win/braidpool/raw/main/proposal/proposal.pdf)
for braidpool.

For details on how delivering shares to market makers for enabling
hashrate futures, read the blog post: [Deliver Hashrate to Market
Markets](https://blog.opdup.com/2021/08/18/deliver-hashrate-to-market-makers.html).

The pool provides:

1. Lower variance for independent miners, even when large miners join
   the pool.
2. Miners build their own blocks, just like in p2pool.
3. Payouts require a constant size blockspace, independent of the
   number of miners on the pool.
4. Provide building blocks for enabling a futures market of hash rates.

# Running the node

For the moment, the node runs a simple p2p broadcast. To run it you need to do
the usual cargo things

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

- [ ] Channel management scripts using libbitcoin.
- [ ] A DAG of shares to track contributions for miners.
- [ ] P2P gossip based broadcast of block and shares.
- [ ] Hub to miner communication using Tor's hidden services.
- [ ] Validate received blocks and shares. We'll need to find a way to
  talk to bitcoin node here for this.
- [ ] Single script installer (limited to Linux variants).


Matrix chat: [https://matrix.to/#/#braidpool:matrix.org](https://matrix.to/#/#braidpool:matrix.org)

Mailing list: [https://sourceforge.net/p/braidpool/mailman/braidpool-discuss/](https://sourceforge.net/p/braidpool/mailman/braidpool-discuss/)

Development blog: [https://blog.opdup.com/](https://blog.opdup.com/)

Donations: bitcoin:bc1q6xms5xsq6kvk9h57mvsdxdjnnrl0vsc942xlxe
