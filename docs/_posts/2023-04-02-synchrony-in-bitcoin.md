---
layout: post
title: "Synchrony in bitcoin"
image: assets/BC_Logo_.png
---

Bitcoin requires nodes to be synchronised within two hours of each
other. Does this mean bitcoin uses a partial synchronous communication
model? The answer is no, because bitcoin does not assume bounds on
message latency or on message processing times at each node.

## What is the clock synchrony requirement in bitcoin?

Bitcoin requires blocks to be mined within a two hour period of the
accepting node's local clock. This is tracked using the
`timestamp_limit_seconds` setting which is set to 7200 seconds - or
two hours.

The above requires that all clocks are synchronised to a tolerance
s.t. `network latency + clock drift < 7200 seconds`

If we ignore network latency since it is much smaller than 2 hours. We
can say that bitcoin requires all clocks to be synchronised to drift
by no more than 2 hours.

## Why does bitcoin require synchronised clocks?

Bitcoin uses a difficulty adjustment algorithm to keep the block
production as close to once every ten minutes as possible.

The algorithm counts the time taken to discover the last 2016 blocks,
and if it was less than two weeks, the difficulty is increased
appropriately. Vice versa difficulty is decreased if it took more than
two weeks to mine the last 2016 blocks.

To make this difficulty adjustment algorithm work it is required that
blocks are accepted as valid only if their timestamp is within a
certain offset from participating nodes. This offset is set to 2 hours
in bitcoin.

## If bitcoin requires synchronised clocks, does it use a synchronous communication model?

The answer is no. Even if bitcoin requires clocks synchronised to
within two hours, the protocols used do not depend on bounds on
message latency or on message processing times. Bitcoin still uses an
asynchronous communication model.
