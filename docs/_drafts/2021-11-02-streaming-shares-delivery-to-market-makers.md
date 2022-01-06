---
layout: post
title: "Streaming shares to Market Makers"
image: assets/BC_Logo_.png
---

## Streaming shares to Market Makers

Hey Kulpreet,

I was discussing the idea of Briadpool with some of my colleagues at River and one had an interesting idea. Do you think it would be possible to stream payments for shares from a market maker to a miner?

For example, I imagine a flow similar to the following. A market maker and miner agree on a price per share, rate of delivery and duration of the contract. The miner would post collateral which would be forfeited if they don’t deliver the shares. The market maker would fully fund a payment channel that would get decremented over time. If the market maker doesn’t pay they forfeit the payment channel. The market maker would also need to be able to claw back the remaining payment channel balance if the miner defaults. I haven’t worked out exactly how this would work with Bitcoin script but was wondering if you had any ideas.

Best,
David

Hi David,

This is exactly the kind of financial tool I hoped we could build on
top of braidpool, and I do think the requirements have to come from
the people closer to market makers than the braidpool 'engineers' can
ever be. So, a big thanks for continuing to explore the possibilities
around braidpool.

The general idea I am thinking about is to tie in the Single Use Seal
into a commitment transaction for a unidirectional payment channel
from market maker (MM) to miner. If the miner tries to double sell the
Single Use Seal, then the MM can see that transaction and has enough
time to broadcast their latest commitment first. With such a time lock
in place, we can then stream the payment from MM to the miner. If the
MM becomes unresponsive then the miner should be able to force close
the channel and get the balance.

I think something is possible here, give me a few days to find some
time to dedicate to this.

I also have some questions in my head about the flow you described.

1. The collateral posted by the miner is forfeited to the market
maker? Just want to be sure I am on the same page.
2. Why do we need the collateral? This might be something from fintech
I am unaware of.
3. The payments from market maker to miner are only dependent on time?
Or should they also include the aggregate difficulty the miner's
shares represent? All this information is available in the shares DAG.
However, this is possibly a future improvement we can add.

Regards,
Kulpreet


Sounds good. Below are my answers to your questions.

1. Yes, in the case that the miner stops mining for the market maker.
2. As an example, if a market maker and miner enter into a 1 week contract and half way through the contract the revenue per TH/s increases to more than the agreed upon price then there is nothing stopping the miner from backing out of the contract to capture the increased revenue elsewhere. It's important that the market maker is assured that if their trade is profitable the miner will live up to their obligation. Similarly, in the payment channel the miner needs to be assured that if the revenue per TH/s goes down then the market maker can't back out of the contract without penalty. In summary, there needs to be an incentive structure in place that both sides live up to their part of the deal as time passes.
3. The difficulty should be included. Maybe a better way to describe what I'm thinking about is that a contract should represent the exchange of Bitcoin and shares for a specified price, rate, and time. An example contract would be for 30 sats for 60TH/minute for 1 week. (I've realized here the rate needs to be standardized to something more intuitive and conceptually 1 share should equal something like 1 EH of work being done).

Best,
David
