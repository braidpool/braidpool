---
title: FROST for Braidpool
layout: post
image: assets/BC_Logo_.png
---

FROST [1] is the most recent threshold signature scheme that sacrifices
robustness for reducing communication complexity. We consider braidpool's
communication model and our requirements from a threshold signature scheme
(TSS). We argue that we braidpool will benefit from FROST's signing phase
without a signature aggregator and that braidpool should use Pedersen's DKG for
robust distributed key generation (DKG). Both of these are suggestions from the
FROST paper.

## Braidpool's Communication Channels

In braidpool, a gossip based reliable P2P broadcast protocol is available for
exchange of shares between miners. This broadcast channel is used for both
reliably broadcasting messages and privately sending messages to individual
miners. Private unicast works by encrypting messages to the receiver. Just as
in LN, the miners in braidpool identify themselves with a public key. This
public key is used to encrypt a private message for a receiver.

### Rounds of Communication

We leave out any timeliness constraints out of this discussion and will consider
them in another post. For now, we assume a round is decided upon by the miners
using synchronised clocks. In a follow up post we will remove this assumption.

## DKG and TSS Requirements for Braidpool

In braidpool we run DKG and a TSS when creating new blocks. The DKG and TSS
outcomes are to be used as:

1. A new public key - The pool uses this public key for the creating coinbase
   transactions. This is the public key which will be spent using a TSS
   execution. We call this key the pool key.
2. Signing UHPO transactions - Miners payouts are tracked using Unspent Hasher
   Payouts (UHPO) [2, 3], which are taproot transactions with time locks. The
   UHPO transaction is used to pay out all miners who have earned rewards from
   previous braidpool blocks. Each UHPO spends the coinbase transaction and the
   UHPO transaction from the last braidpool block that was confirmed as a
   bitcoin block. We need to run the signing phase matching the DKG that was run
   to generate the previous coinbase. We sign the UHPO transaction with this
   block's pool key.

In Braidpool we generate a pool key that is later used to sign transactions. We
also sign a transaction with an older pool key. Therefore, we require that the
protocol be robust to handle relatively large delays between the generation of
pool key and its use for signing during which time the set of active miners can
change.

Consider the situation where at time $T_1$ the set of miners $M_1$ generate a
pool key, $PK_{M_1}$. Once the set of miners changes, say to $M_2$, a new round
of DKG is run to generate $PK_{M_2}$. The new UHPO transaction spends the
previous UHPO transaction as well as the previous block's coinbase. To handle
this, the miners run a DKG to generate the new pool key and run the signing
protocol with the previous cohort of miners to spend the previous coinbase
transaction and the previous UHPO transaction.

This shows that our choice of DKG and TSS protocols should support:

1. **Robust signing phase** - This is required to handle the situation where the
   set of miners participating in two consecutive bitcoin blocks change. We will
   run the signing phase of the TSS scheme with the previous set of miners.
   1. FROST's efficient signing protocol helps us here. By running the DKG and
      the preprocessing phase to generate a single set of nonces at the same
      time. The signing phase will then run with the miners set $M_{signing} =
      M_1 \cap M_2$ as long $|M_{signing}| > 2/3 * |M_1| + 1$.
2. **Robust DKG phase** - The DKG protocol has to finish in the presence of
   misbehaving nodes that can block braidpool's progress. That is we need the
   DKG protocol to be robust. The FROST paper chooses a non-robust DKG because
   in their use case the participants will need figure out the problem out of
   band and restart the DKG. We instead need the DKG to proceed even under an
   attack by a participant. We propose using Pedersen's DKG. The FROST paper
   makes the same recommendation to implement a robust DKG protocol.

### Signature Aggregator

FROST also proposes using a Signature Aggregator elected from the set of
participating signers. They suggest that applications that don't want this
centralisation pressure should use a broadcast channel to aggregate the final
signature on all participating signers. This results in an increased
communication cost and we accept this cost to avoid a bad actor being elected as
the signature aggregator and potentially disrupting the workings of Braidpool.

Since braidpool has a broadcast channel available, we will use the broadcast
approach to get the threshold signature on all miners.

## Conclusion

We have made the following decisions when running FROST threshold signature
scheme:

1. DKG - Use Pedersen's DKG
2. Signature - Use FROST scheme without the signature aggregator

## References

[1] [FROST](https://crysp.uwaterloo.ca/software/frost/)
<br/>[2] [Braidpool specs](https://github.com/mcelrath/braidcoin/blob/master/braidpool_spec.md#unspent-hasher-payment-output)
<br/>[3] [Generating pool key and blocks to mine](https://blog.opdup.com/2023/08/09/block-generation.html)
