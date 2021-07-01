---
layout: post
title: "Can P2Pool Do What Braidpool Does?"
image: assets/BC_Logo_.png
---

Just like [P2Pool](http://p2pool.in/), Braidpool uses peer to peer
communication between miners to track PoW shares. The question then
is, can we extend P2Pool to achieve the goals of Braidpool? In this
post we present how Braidpool is different from P2Pool and why
Braidpool is a new implementation from scratch.

There are a few components that come together to provide the goals of
Braidpool. Before we go into those components, a quick reminder of the
goals of Braidpool:

1. Reward miners for all their PoW shares.
2. Scale to tens of thousands of miners.
3. Provide infrastructure for building financial tools to help miners manage risk.

To achieve these goals, braidpool needs the following components to
work together:

1. A peer to peer network of miners to disseminate shares.
2. A rewards calculation algorithm that incentivizes miners to
   disseminate them at the earliest.
3. Payment channels to make payouts to miners so that a constant
   amount of blockspace is required, independent of the number of
   participating miners.
4. An anonymous hub that can't deny rewards payouts to miners.

## Peer to Peer Network and Finding Shares

Just like P2Pool, miners participating in Braidpool broadcast their PoW
shares to other miners over a p2p network.

In P2Pool the network difficulty is adjusted so that the pool finds
one share every 30 seconds. This results in smaller miners struggling
to find a share and makes P2Pool economically nonviable for them.

In Braidpool, this is not the case. Each miner participating in
Braidpool can choose the difficulty they mine at so that they generate
a share at an interval of their choosing. Small miners will mine at
low difficulty to generate a share every 10 seconds, while large
miners will mine at a much larger difficulty to find a share every 5,
10, or 20 seconds. Both the difficulty and the share period can be
configured by the miner.

Since small miners are able to find shares at their chosen
difficultly, they can claim rewards for all their PoW shares.

## Rewards Calculation - No More Orphans and DoA Shares

With miners choosing their own difficulty, the rewards calculation
algorithm in Braidpool takes into account the difficulty used by the
miners when they find their shares.

This rewards calculation algorithm incentivizes miners to broadcast
shares as soon as they discover them. The details of the rewards
calculation algorithm are described in detail in the
[proposal](https://github.com/pool2win/braidpool/blob/main/proposal/proposal.pdf)
under review.

This is contrast to how in P2Pool each miner has to generate shares
using the same difficulty. As the network grows, the difficulty
increases and smaller miners are forced out of the network. This
dynamic that limits the growth of P2Pool is absent in Braidpool. As
more miners join Braidpool, each miner is still rewarded for all their
PoW shares, and in fact, each miner is rewarded more frequently since
the pool can find blocks more frequently.

## Miner Payouts with Payment Channels

In P2Pool, all miners that found a share for a bitcoin block are
rewarded in the coinbase of the next bitcoin block the pool finds. The
rewards are paid out through the coinbase of the next block. The
problem is that as more miners find shares, the size of the coinbase
transaction keeps growing. The increasing size of the coinbase reduces
the profitability of P2Pool from finding a block. Also miners now have
to aggregate their UTXOs for each reward and thus further increases
the costs for the miners.

Chris Belcher first proposed the idea of using Payment Channels in a
[BitcoinTalk post](https://bitcointalk.org/index.php?topic=2135429.0)
to make payments to miners for their PoW shares, and Braidpool uses
Payment Channels to distribute payouts to miners.

This means that Braidpool's coinbase transaction are of a constant
size and do not need more blockspace as more miners join the pool. It
also amortises the costs for miners to spend their rewards earned for
PoW shares from multiple blocks.

## A Hub For Miner Payouts

Unlike P2Pool, Braidpool requires a hub to open channels for miner
payouts and then to make payouts to the miners. However, the payment
channels are constructed in a way that neither the miner nor the hub
can cheat. The proposal and the bitcointalk post by Belcher describe
the channel construction in detail and show how neither the miners,
nor the hub can cheat or without payouts.

Since the hub can be attacked, the hub use Tor v3's hidden
services. Being a Tor hidden service, the hub's location is hard to
detect and the hub can resist DDoS attacks.

## Conclusion

Braidpool uses completely different mechanisms to manage shares,
calculate miner rewards and distributing the payouts. The changes are
across the entire 'stack' and this motivates the need to rethink and
implementation from the ground up.
