---
layout: post
title: "P2P Connection Lower Bounds"
image: assets/BC_Logo_.png
---

Apart from the standard requirements of a P2P node, braidpool will
require that all nodes are connected to `log_10(N)` peers when the
network size is `N`. The reason for this requirement is to provide
fast message propagation across the network while paying the cost of
higher resource requirement at each node.

`log_10` connections will enable each hop to result in message
reaching 10x the number of nodes, potentially requiring four hops to
cover a network of 10,000 nodes in a large braidpool instance.

The challenge here is how do we make sure that nodes connect to a
lower bound number of nodes?

There are a few possibilities where neighbouring nodes sign tickets
for each node certifying they have a bidirectional connection. We
might not even need this strict policy, but I am leaving it here to
suggest there are potential solutions to this requirement.

