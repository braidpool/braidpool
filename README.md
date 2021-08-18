
![Build status](https://github.com/wholooks/braidpool/actions/workflows/cmake.yml/badge.svg)

# Proposal

Read the
[proposal](https://github.com/pool2win/braidpool/raw/main/proposal/proposal.pdf)
for braidpool.

For details on how delivering shares to market makers for enabling
hashrate futures, read the blog post: [Deliver Hashrate to Market
Markets](https://pool2win.github.io/braidpool/2021/08/18/deliver-hashrate-to-market-makers.html).

The pool provides:

1. Lower variance for independent miners, even when large miners join
   the pool.
2. Miners build their own blocks, just like in p2pool.
3. Payouts require a constant size blockspace, independent of the
   number of miners on the pool.
4. Provide building blocks for enabling a futures market of hash rates.

# Progress

The [project on github](https://github.com/wholooks/braidpool/projects/1)
tracks the main components to build. Here's a list to keep us focused:

- [ ] (WIP) Channel management scripts using libbitcoin.
- [ ] A DAG of shares to track contributions for miners.
- [ ] P2P gossip based broadcast of block and shares.
- [ ] Hub to miner communication using Tor's hidden services.
- [ ] Validate received blocks and shares. We'll need to find a way to
  talk to bitcoin node here for this.
- [ ] Single script installer (limited to Linux variants).

Donations: bc1q6xms5xsq6kvk9h57mvsdxdjnnrl0vsc942xlxe
