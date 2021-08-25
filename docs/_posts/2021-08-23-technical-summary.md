---
layout: post
title: "Braidpool: Technical Summary"
image: assets/BC_Logo_.png
---

This post provides a technical summary of how Braidpool works. There
are three main components to braidpool 1) a DAG of shares to track
work done by miners and calculate rewards, 2) one-way payment channels
for payments with fixed blockspace requirements and 3) Single Use
Seals to trade miner shares on an open market. The detailed proposal
can be found
[here](https://github.com/pool2win/braidpool/raw/main/proposal/proposal.pdf).

First a quick reminder of the goals of braidpool:
1. Low variance for independent miners, even when large miners join
   the pool.
2. Miners build their own blocks.
3. Payouts use a constant amount of blockspace.
4. Provide tools for enabling a hashrate futures market.

## How Does Braidpool Work?

There are three main components to braidpool 

1. A DAG of shares maintained on a P2P network to track work done by
   miners and calculate rewards,
2. One-way payment channels for payments with fixed blockspace
   requirements and
3. Single Use Seals to trade miner shares on an open market.

### P2P Network of Miners

All miners join a P2P network and build their own blocks. These blocks
are broadcast to the P2P network by each miner as their target
work. When shares are found by a miner those are also broadcast to the
P2P network. Miners that receive shares from other miners validate the
share using the block announced by the miners as their work.


### DAG of Shares

Braidpool builds a DAG of shares, so each share is tracked as a node
in the DAG with hash pointers between shares providing a partial order
between shares. These hash pointers from each share point to the head
of the DAG when the miner found the share. This eventually consistent
partial ordering of shares enables us to reward all shares found by
miners using the rewards calculation described later.

Each share in the DAG is then rewarded for contributing to the
pool. This is different from P2Pool's 30 second block time, where one
block wins and all other miners lose. The approach of 30s block time
hurts small miners as large miners join the pool.

### Miner Defined Difficulty

Each miner chooses its own difficulty to produce shares at their
chosen target rate. Given the studies into block propagation time, a
rate of generating a share every 10 seconds seems reasonable for
now. Small miners will configure their braidpool node to produce work
that requires low enough difficulty to produce one block per 10s,
while large miners will select a larger difficulty.

Miner defined difficulty is set in the coinbase, so it can't be set
arbitrarily by the miner but is defined as part of the block.

### Reward Calculation

The reward scheme is similar to [Laurentia
Pool's](https://pool.laurentiapool.org/) Score Per Last N Shares
(SPLNS). Since each miner works at its own defined difficulty, each
share is weighted by the difficulty it was found at, and then rewards
are distributed using the Last N Shares found on the pool.

Using a PLNS based scheme resists pool hopping, while using a score
that takes into account the miner defined difficulty and thus rewards
miners according to the amount of PoW they produce.

### Payment Channels

The goal of the payment channels is to reduce the block space required
to make miner payouts. However, it is also required that no
participant is able to cheat and steal money or hold the miners
ransom. There is another requirement that the entity organising the
payment channels, called the hub, can resist attacks to censor or shut
down the pool.

The payment channel construction achieves these goals by:

1. The channel transactions and coinbase transactions are inter-linked
   using preimages such that stealing money is impossible. The hub can
   go rogue and stop sending rewards to miners, but it will be hurting
   its own profits by doing so and miners can still claim the reward
   by non-cooperatively closing the channel.
2. Hub creates a funding transaction and charges 10-50bp in fees from
   miners for doing so.
3. Hub and miners communicate using tor's hidden services.

### Dynamics of Hub and Miner Defection

As far as we have analysed, the dynamics of interaction between hub
and miners to hurt the other don't work in favour of anyone. However,
if the hub is discovered and attacked by a censor, the miners have a
chance to close channels, receive payouts due up to that point and
reorganise under a different hub.

### Providing Tools for Trading Shares

Since shares are available on a P2P network, we can build tools to
trade shares for BTC using Single Use Seals. The details are on [this
blog post]({% post_url
2021-08-18-deliver-hashrate-to-market-makers%}). Once shares can be
traded, we can engage market makers to provide futures contracts for
mining shares.

### Revenue for the Hub

Since the hub funds the channels, it charges a small fees for the
same. We expect this fees to be around 10-50 basis points.

## Conclusion

We described the various components of braidpool and how they work
together. We will soon follow up with another blog post with a system
architecture for braidpool.
