---
layout: page
title: "Specification"
image: assets/BC_Logo_.png
---

List of specifications in TLA+:

1. [P2P Broadcast]({{ site.baseurl }}{% link /specifications/P2PBroadcast.pdf %})
1. [Shamir Secret Sharing]({{ site.baseurl }}{% link /specifications/ShamirSecretSharing.pdf %})
1. [Miner share accounting and block generation]({{ site.baseurl }}{%link /specifications/BlockGeneration.pdf %}) We specify how
   broadcast shares are accounted for towards miner payouts. When a
   bitcoin block is found, all unaccounted for shares are added to
   miners Unspent Hasher Payout (UHPO). We do not spec out how the
   distributed key generation algorithm is run - instead we replace the
   public key for coinbase payout to simply be the concatenation of
   the miner id.
1. The above spec for block generation uses the [Bitcoin Transactions]({{ site.baseurl }}{% link /specifications/Bitcoin.pdf%}) spec.
   The transaction spec uses a simple scriptSig = scriptPubkey check.


List of protocols still to be specified:

1. Pedersen's DKG using the P2P Broadcast
1. Block coinbase and UHPO transaction constructions
1. Generating threshold signature to update UHPO transactions
1. Miner cash out protocol
