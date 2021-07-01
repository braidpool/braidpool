---
layout: post
title: "What is the Braidpool Hub?"
image: assets/BC_Logo_.png
---

## A Hub For Miner Payouts

Unlike P2Pool, Braidpool requires a hub to open channels for miner
payouts and then to make payouts to the miners. However, the payment
channels are constructed in a way that neither the miner nor the hub
can cheat. The proposal and the bitcointalk post by Belcher describe
the channel construction in detail and show how neither the miners,
nor the hub can cheat or without payouts.

No matter which transactions the miner chose to include in its block,
the hub can't deny payouts to miners. If the hub does not pay the
miner, the miners can spend from their latest channel updates and
close their channels with the hub. In the proposal, it is suggested
that the hub charges a fees for funding the payment channels to
miners. If all miners close their channels and abandon the hub, the
hub loses the stream of revenue and the miners can re-organise under a
new hub.

It is also important to note that the hub can't deny payment to a
single miner. With the way the payment channels and the coinbase are
constructed, the miner that finds the block requires that the hub
updates the state of payment channels to all the the miners. If a
single miner is not paid, all the miners will abandon the hub.

Since the hub can be attacked, the proposal recommends that the hub
use Tor v3's hidden services. Being a Tor hidden service, the hub's
location is hard to find out and the hub protects itself from
potential DDoS attacks.
