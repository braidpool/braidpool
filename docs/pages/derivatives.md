# Bitcoin Hashrate Derivatives Trading

## Introduction

In well developed commodities markets, _derivatives_ trading is a fundamental
tool used by producers of the commodity to hedge their risk. On one side of the
trade is the commodity producer and on the other side is a risk-taker. In the context of bitcoin we will call these two entities the _miner_ and _risk-taker_.

The producer of a commodity knows how much corn he's planted, oil wells he's
drilled, or bitcoin miners he's plugged in. What he doesn't know is how much of
the commodity he will produce. In the corn market this is a function of the
amount of rain or other weather-related phenomena that affect the growing
season. In the oil market a well may run dry, or a cold winter may change the
demand for heating oil.

In bitcoin there is revenue variance for miners in the form of the number of
blocks the pool wins (called "luck" on mining pool stats), the fees in
transactions from those blocks, and the number of shares produced by the miner.
These are outside the control of the miner and miners could improve the
financial viability of their operation and access to capital by hedging against
these risks. What the miner knows is how many devices he has and how much it
costs to run them, which gives him a handle on how many hashes (hashrate * time)
he can produce in a given time.

While fees are a conceptually different revenue stream than block rewards, herein we will refer to a "hashrate derivative" as a contract that hedges all revenue from mining including both fee variance and block variance.

## Hashrate Derivatives Emulate FPPS

A contract can be made between a miner and a risk-taker using an [ISDA Master
Agreement](https://en.wikipedia.org/wiki/ISDA_Master_Agreement). This would
specify the number of hashes the miner expects to produce (which is
hashrate*time), expected payment schedule by the risk-taker, curtailment
expectations by the miner, and any other details. After hammering out the
contract, these two counterparties can repeatedly execute the contract given the
negotiated terms. This means a payment from the risk-taker to the miner, and
proof from the miner that he has run his mining operation as the master
agreement describes, which in essence is proof of the number of hashes he
computed. This is an example of a fixed-for-floating swap, where the miner takes
a fixed payment and the risk-taker takes a floating payment.

Miners have [expressed a strong preference for FPPS and
PPS](https://medium.com/@SpiderPool_com/exploring-bitcoin-why-full-pay-per-share-fpps-reigns-supreme-cefac721238d)
in which they receive a fixed income per share. One can emulate FPPS even if the
miner is not using an FPPS pool by engaging in a derivatives contract as
described above. For instance, a miner could mine on the [OCEAN
Pool](https://ocean.xyz/) which is a PPLNS variant called
[TIDES](https://ocean.xyz/docs/tides). A miner mining on this pool and using
[DATUM](https://ocean.xyz/docs/datum) is helping decentralize the network by
constructing block templates, but the OCEAN pool has [only won 0.4% of blocks
over the last 1000 blocks](https://miningpoolstats.stream/bitcoin) as of Nov 26,
2024. This means that the miner has roughly a 25% variation in their revenue per
two-difficulty adjustment periods (about a month). A 25% variation in your
revenue can be hard to handle. This means that in a calendar year, this miner
will have on average two months where his revenue is 25% or more below
expectation and two months where it is 25% or more higher.

By engaging in a hashrate derivatives contract with a risk-taker, practically
the miner mines to the risk-taker's bitcoin address instead of his own, and gets
paid directly by the risk-taker instead. This can also be a bitcoin transaction
but it could be any form of financial settlement (if for instance the miner
wanted dollars or another currency instead).

Thus the consistent revenue of FPPS can be achieved with a market-based mechanism, with a competitive market of risk-takers. Having a competitive market will drive down fees and reduce capital requirements for both miners and pools.

The risk-taker performs a professional risk analysis of the expected production
and other market considerations like demand. In the case of bitcoin mining the
risk-taker needs to figure out how much he might earn and price the contract. He might take into account:

1. Hashrate of the upstream pool
2. Expected new mining sites and power contracts
3. Number of ASICs taped out, assembled, shipped or installed
4. Fee variance from e.g. shitcoin projects (BRC-20, Runes, monkey JPEGs)
5. Expected curtailment due to weather or other power grid changes
6. Energy price in the relevant power market and changes due to e.g. new generation or transmission facilities
7. BTCUSD price (which can be separately hedged using [options and futures](https://www.cmegroup.com/markets/cryptocurrencies/bitcoin/bitcoin.contractSpecs.html)) on traditional markets.

He then prices the contract payment to the miner and includes a fee for himself
for this service. The risk-taker is expected to be well-capitalized and able to
financially weather the "unlucky" times. Different risk-takers will reasonably
have different opinions on the hash price, and their risk models are
proprietary and based on expertise and information they can gather.

## Auditing The Miner

In order to service the contract, the miner needs to prove to the risk-taker
that he is mining according to the terms of the contract. This doesn't mean that
he has a 100% uptime as the contract can specify terms that allow the miner to
curtail or underclock during high-energy price times. Miners that might do this
are becoming more common as they're often consuming renewable energy like wind
or solar which is over-produced at times. Nonetheless the miner needs to prove the number of hashes delivered.

Currently Foundry and NYDIG run pools specifically for the purpose of monitoring
the terms of _loan_ contracts. Running a pool specifically for this purpose is
an expensive loss leader, and we'd be better off with an open source, general
purpose method to monitor mining that could also be used to monitor hashrate
derivatives contracts.

One might execute such a contract by simply monitoring the pool payouts, but
this is a low-statistics measurement of the delivered hashrate and subject to
exactly the kind of variance the risk-taker is supposed to be hedging, and he
needs a more precise measurement. For some pools it may be possible for the
risk-taker to connect to the pool as an observer and see a given customer's
hashrate. However anecdotal evidence indicates that miners on most FPPS pools
are getting paid 5-7% less than expected, for unknown reasons. It's not
generally possible to audit an _entire_ centralized pool and all their _other_
customers to know what the total hashrate is. One might get a measurement of one
miner's hashrate but the risk-taker is exposed to counterparty risk from the
pool itself, which could be fudging the numbers.

## What Happens Today

In effect, today's centralized mining pools are acting as risk-taker, and must
be well capitalized to do so. These capital requirements are fairly extreme,
leading to smaller pools making deals with bigger pools (specifically Antpool)
to financially cover them. Any such agreement between pools is a private
agreement so we can't know the details, but evidence of this was uncovered by
[@0xb10c](https://x.com/0xb10c) and [detailed in his
blog](https://b10c.me/observations/12-template-similarity/).

## The Future

The Braidpool project will use a Directed Acyclic Graph (a blockchain where each
block can have multiple parents) to collect and audit shares. A risk-taker can
then connect to the braidpool node being used by the miner to audit the number
of shares delivered in a provable and secure manner, secured by Bitcoin's
proof-of-work itself. In this "audit-only" mode which will be our first release,
Braidpool will act as a [StratumV2 proxy](https://stratumprotocol.org/) and
require an upstream pool. We will work with prospective risk-takers to integrate
this node software into their infrastructure, create their proprietary risk
model, and engage in any necessary transactions such as receiving shares from
the miner, sending bitcoin to the miner, or engaging in Discreet Log Contracts
(DLC's) to settle the contract. Later versions of Braidpool will additionally
manage payouts to the miners or risk-takers, eliminating the need for an
upstream pool while keeping strong auditability.

Braidpool will also move block template construction and transaction selection
directly to the miners, improving censorship resistance and decentralization
while at the same time improving the revenue of miners and pools that run on top
of Braidpool.

In essence, Braidpool will separate these four logically distinct roles in the bitcoin mining ecosystem:

1. Transaction Selection (miners running bitcoind)
2. Risk Management (risk-taker counterparties)
3. Payment processing (braidpool software)
4. Miner monitoring (braidpool software)

We hope to get a first "audit-only" version of Braidpool out within a few
months, but it's important to note that even today, miners and risk-takers could
be engaging in hashrate derivative contracts using a pool like OCEAN with low
counterparty risk but high variance. Risk traders are leaving a lot of money on
the table by letting centralized pools take it all. Until Braidpool is ready, we
recommend that miners use OCEAN or DEMAND and attempt to hedge their risk by
engaging a risk taker.

Miners or prospective risk-takers (share buyers) can find us on
[Discord](https://discord.gg/pZYUDwkpPv) in the [#hashrate-derivatives](https://discord.gg/PVRstVK5db) channel to discuss further.
