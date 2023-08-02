---
layout: post
title: "Lighting Network's Liveness Guarantees"
image: assets/BC_Logo_.png
---

OBSOLETE: I was going down the incorrect line of thinking. It is not
the concurrent access to liquidity, but some other unknown reasons.

# LN payment liveness guarantees

LN payment routing and forwarding provide liveness properties that
depend on HTLC expiry. For example, a payment sent by a node along a
route can sometimes be stuck. Depending on the length of the
forwarding route such payments be stuck for a long time as each HTLC
along the route expires. In this post, we propose that LN should
provide safe ways to access each node's liquidity - this will help
less payments to get stuck.

One can argue that stuck payments are not that widespread. However, if
LN has to forward millions of payments a day, we need to eliminate
such known issues.

In this post we argue for a protocol to provide LN payment liveness
guarantees using the LN communication protocol and not just depend on
HTLC's lock expiry.

# Payment failures

Forwarding a payment can fail due to a number of reasons. The obvious
ones are:

1. a node could fail to forward payment because the downstream node
has gone offline or
2. a node's own liquidity has run out by the time the payment to be
forwarded arrives at it.

The falling node mechanism can only be addressed by using a failure
detection mechanism like a timeout on the sending node, etc. [2] As
far as I can tell, the failure detection currently works at the level
of lightning bitcoin scripts level. That is, we need to wait for the
timelock to expire.

In this post, we focus on the second failure - a node's liquidity runs
out before an HTLC to be forwarded arrives. Such a failure occurs
because each routing node's liquidity is accessed concurrently in an
unsafe manner.

# Unsafe access to node's liquidity

Two or more sending nodes can choose to route a payment through node
`f`. However, the first payment might consume 

This unsafe concurrent access to a routing node's liquidity results in
payments failing and the nodes involved having to wait for HTLC expiry
to know about the failure.

There might be a very simple approach that prioritises payment
reliability, while reducing emphasis on latency and fees.

The idea must have been discussed before and maybe then abandoned. I
can't find the discussion on lighting-dev mailing list. Most
discussion is about improving route finding for increased reliability
[1].

Here's a high level idea:

Each node along a route first locks their liquidity away for a payment
and then forwards a similar lock liquidity request. Nodes then forward
the HTLC only if they receive an ack for their request to lock
liquidity from the downstream node.

If they receive a nack from their downstream node or the request times
out, the node unlocks the liquidity associated with the payment and
sends a nack upstream.

This is how it will work:

1. An initiating node determines a payment route, say, n1, n2, n3 is the route.
2. Before sending the payment, node n1 sends a "lock liquidity"
   request. This request asks n2 to lock their liquidity for a time
   period t.
3. In response, n2 can:
   3.1. reject the lock request and send a nack to n1.
   3.2. timeout and not send a response to n1.
   3.3. forward a lock request to n3 and wait for ack.
4. If any node receives a nack from the downstream node, it unlocks
   their liquidity and sends a similar nack to their upstream node.

I am curious to know more about how payment reliability is built into
the LN protocol, and if similar approaches were discussed and not
pursued because they were vulnerable to attacks.

One obvious attack is a node can ask for a large number of nodes on
the network to lock liquidity. An obvious fix here is that the lock on
liquidity has a timeout.

A detail to note is that all these timeouts do not require clocks to
be synchronised between nodes, and these timeouts are all local to
each of the nodes.


[1] https://lists.linuxfoundation.org/pipermail/lightning-dev/2021-November/003342.html

[2] https://github.com/lightningnetwork/lnd/issues/2786#issuecomment-474190486
