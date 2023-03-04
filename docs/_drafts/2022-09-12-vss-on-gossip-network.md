---
layout: post
title: "Verifiable secret sharing on a gossip network with streaming events"
image: assets/BC_Logo_.png
---

In this post we introduce the gossip protocol for braidpool and show
how a VSS protocol can be implemented for braidpool with no additional
communication rounds complexity. We do need to pay the price of extra
data being communicated, so the bits communication complextiy is
non-zero. The gossip protocol for braidpool has to support periodic
broadcasts from all nodes of the shares found. These broadcasts form a
DAG of message dependency relationships. These dependency
relationships help us build a reliable broadcast. We build on this
base communication layer to provide an implementation of verifiable
secret sharing with zero overhead - avoiding the $O(n^3)$ complexity.

# VSS requirements on braidpool

Braidpool will benefit from a scalable implementation of Schnorr
threshold signature that can scale across the miners participating in
the network. Ideally, we want a braidpool instance to scale to least a
thousand miners.

Threshold signatures build upon a verifiable secret sharing (VSS)
scheme to provide distributed key generation (DKG). VSS has been
studied in network model with broadcast ability and has been known to
scale with $O(n^3)$ complexity. With some optimisations using a gossip
broadcast network the complexity is shown to still be $(n^2) at best.

We show how using a braidpool network model with steady periodic
updates from honest miners can be used to build a VSS implementation
without requiring any extra rounds of communication.

# Periodic shares broadcasts on braidpool

In braidpool, all miners generate shares at a known frequency. If a
miner doesn't generate a share all other miners can detect the absence
of shares from the miner as a signal that the miner failed.

Since we depend messages from a miner eventually reaching all miners,
we need to be mindful in avoiding eclipse attacks on a miner by other
dishonest miners.

# Piggyback VSS messages on share messages

# Gossip protocol for braidpool

## Node Identity

## Handshake

## Peer Discovery

### Connection limits

### Drop connection rules

### Connection rules

## Share broadcast

### Origin share

### Forward share

