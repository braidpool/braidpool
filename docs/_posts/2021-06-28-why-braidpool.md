---
layout: post
title: "Why Braidpool?"
image: assets/BC_Logo_.png
---

Current mining pools can be forced into censoring transactions and
their opaque accounting limits their use for building financial tools
that can help miners manage their business risks. This post briefly
discusses the limitations of centralised mining pools and provides
motivation to build Braidpool.

## Censorship Resistance

If the only mining pools are like today's centralised mining pools, a
censor has a straight forward path to censor transactions.

When a censor wants to censor some transactions, it reaches out to
centralised pool operators and forces them to exclude censored
transactions from their blocks.

One way to resist this censorship is for the transaction author to
keep increasing the fees on the transaction until some miner picks up
the transaction at the risk of being targeted by the censor. See
[Censorship Resistance
Property](https://github.com/libbitcoin/libbitcoin-system/wiki/Censorship-Resistance-Property).

[Stratum v2](https://braiins.com/stratum-v2) allows miners to build
their own blocks and therefore a censor can not directly ask a
centralised pool operator to censor transactions. However, the censor
can still force the pool operators to refuse payouts to miners for
blocks that include a censored transaction.

Braidpool is designed to resist such censorship attacks. Read the full
[proposal](https://github.com/pool2win/braidpool/blob/main/proposal/proposal.pdf)
under review for details.

## Futures Markets

Miners and market makers have shown an interest in developing a market
of hashrate futures contracts. Using such contracts, miners manage
risk and market makers earn revenue while helping the Bitcoin mining
industry.

Building a futures contracts market across mining pools faces the
problem of trusting the pool operators to honestly report their
hashrate at all times.

With Braidpool the hashrate is published on a global peer to peer
network. The published record is the same verified record that
Braidpool uses to compute rewards for miners. Market makers can use
the same record to create futures contracts that pay miners in
exchange of verified proof of work.

Braidpool is also developing solutions for miners to deliver hashrate
to market makers such that the hashrate can only be traded once. Such
tools are simply not possible to build on current centralised pools.

## Hashrate contracts

Some of the current mining pools publish Hashrate contracts
(e.g. [poolin](https://mars.poolin.fi/#/)) that can be bought to earn
a yield based on the pool's hashrate.

Anyone who buys these hashrate certificates representing a fixed
amount of hashrate on the pool can earn payouts as the mining pool
earns mining rewards.

The problem is again, the lack of transparency on the accounting and
the need to trust the centralised pools to publish their hashrate
accounts.

With Braidpool, all the hash rate of participating miners is
transparently visible to anyone. This enables building Hashrate
contracts that don't need a trusted pool operator.
