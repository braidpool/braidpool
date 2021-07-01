---
layout: post
title: "Why Braidpool?"
image: assets/epoch.png
---

Current mining pools can be forced into censoring transactions and
their opaque accounting stifles the ability to build tools for
building financial tools to help miners manage risk. This post
discusses the limitations of centralised mining pools and provides
motivation for building Braidpool.

## Censorship Resistance

A censor has a straight forward path to censor transactions if the
only mining pools are like today's centralised mining pools.

If a censor wants to censor some transactions, it reaches out to
centralised pool operators and forces them to exclude censored
transactions in their blocks.

One way to resist this censorship is for the transaction author to
keep increasing the fees on the transaction until some miner somewhere
picks up the transaction at the risk of being targeted by the
censor. See [Censorship Resistance
Property](https://github.com/libbitcoin/libbitcoin-system/wiki/Censorship-Resistance-Property).

[Stratum v2](https://braiins.com/stratum-v2) allows miners to build
their own blocks, which removes the ability for a censor to contact a
centralised pool operator to censor transactions. However, the censor
can still force the pool operators to refuse to make payouts to miner
for blocks that includes a censored transaction.

## Hashrate contracts

Some of the current mining pools publish Hashrate contracts
(e.g. [poolin](https://mars.poolin.fi/#/)) that can be bought to earn
a yield based on the pool's hashrate.

Anyone who buys these hashrate certificates representing a fixed
amount of hashrate on the pool can earn payouts as the mining pool
earns mining rewards.

The problem is the lack of transparency on the accounting and the need
to trust the centralised pools to publish their hashrate accounts for
audits.

Braidpool is working on a solution where all the hash rate of
participating miners is transparently visible to anyone and therefore
enables building Hashrate contracts that don't need a trusted pool
operator.

## Futures Markets

Miners and market makers are interested in developing a market of
hashrate futures contracts. Miners will be able to manage risk using
such futures contracts and market makers will earn revenue while
helping the Bitcoin mining industry.

To build a futures contracts market across mining pools faces the
problem of trusting the pool operators to honestly report their
hashrate at all times.

With Braidpool the hashrate is published on a global peer to peer
network and market makers can create futures contracts that can pay
miners in exchange of proof of work published on Braidpool.
