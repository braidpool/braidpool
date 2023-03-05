---
layout: post
title: "Need for specifications"
image: assets/BC_Logo_.png
---

We have started a discussion around writing down specifications for
braidpool. This is motivated by the need to clarify the details in our
own heads as we build braidpool, but also to enable contributions to
braidpool.

Before we can specify the entire stack, we need to identify the layers
that make up braidpool. Only then we can specify each layer
individually. This will help us to clearly separate the different
components. In turn, this gives us the advantages of separating
implementations with well defined boundaries.

The layers, informally are:

1. P2P nodes
   1. P2P channels between nodes
   2. Broadcast over P2P
1. Share definition (simply a record)
1. Eventually consistent view of messages exchanged
1. Accounting formula over the eventually consistent view
1. UHPO view - using the eventually consistent view and the accounting formula
1. Updates to UHPO - when do these updates get triggered? What is the change?
   1. Payout transaction - structure of the transaction
   1. Payout transaction - how does this change the UHPO structure?
   1. Payout transaction - how do miners check out and leave the
   network? How does the payout transaction change in response?
1. Delivery of shares - transacation constructions and effects
