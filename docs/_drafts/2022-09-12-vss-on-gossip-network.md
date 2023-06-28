---
layout: post
title: "Efficient verifiable secret sharing on gossip networks"
image: assets/BC_Logo_.png
---

In this post we introduce a verifiable secret sharing (VSS) scheme
build on a gossip broadcast protocol and show that the VSS adds no
message complexity. We still communicate extra data, so the bits
communication complexity is non-zero.

# Background

The gossip protocol for braidpool is used for periodic broadcasts from
all nodes of the shares found. All nodes are connected only to a
handful of neighbours, about $ln(n)$ for a network with $n$ nodes[1].

The messages broadcast form a directed acyclic graph of message
dependency relationships. These dependency relationships help us build
a reliable broadcast which assumes an asynchronous network and does
not address Byzantine failures.

The broadcast is not resistant to Byzantine failure of nodes. The
layer above the the broadcast layer is responsible for handling
byzantine failures. This layer above the broadcast layer is verifiable
secret sharing and we present a protocol with zero communication
overhead for the VSS messages. All messages to reach the VSS are piggy
backed on the shares broadcast by miners.

# VSS requirements for braidpool

Braidpool will benefit from a scalable implementation of a Schnorr
threshold signature scheme that can scale across the miners
participating in the network. Ideally, we want a braidpool instance to
scale to the order of 1000s of miners.

Threshold signature schemes depend on an implementation of verifiable
secret sharing (VSS) scheme to provide distributed key generation
(DKG). VSS has been studied in network model with broadcast ability
and has been known to scale with $O(n^3)$ complexity [TODO: ref]. With
some optimisations using a gossip broadcast network the complexity is
shown to still be $O(n^2)$ at best [TODO: ref].

We show how using a braidpool network model with steady periodic
updates from honest miners can be used to build a VSS implementation
without requiring any extra rounds of communication.

Recent works [TODO: ref ROAST] on providing Schnorr Threshold
Signatures use the idea of multiple sessions of TSS running in
parallel to generate a threshold signature with $t$ out of $n$ parties
collaborating to create a threshold signature. ROAST allows $t$ and
$n$ to be set to arbitrary integers, as in there is no requirement
that $n = 3t + 1$.

# Periodic shares broadcasts on braidpool

In braidpool, all miners generate shares at a known frequency. If a
miner doesn't generate a share all other miners will detect the
absence of shares from the miner as a signal that the miner failed
[TODO: Ref: Unreliable Failure Detectors for Reliable Distributed
Systems]. As more miners join braidpool and the hashrate goes up, the
minimum difficulty miners use to generate their shares increases -
i.e. miners adjust their difficulty to make sure the frequency of the
shares (share generation rate) stays within bounds to avoid being
detected as having failed by other nodes in the network.

Since we depend on messages from a miner eventually reaching all
miners, we need to be mindful in avoiding eclipse attacks on a miner
by other dishonest miners.

# Piggyback VSS messages on share messages

VSS and DKG d

# References

[1] [Epidemic algorithms for replicated database
maintenance](https://dl.acm.org/doi/10.1145/43921.43922) Demers, Alan;
Greene, Dan; Hauser, Carl; Irish, Wes; Larson, John (1987).
