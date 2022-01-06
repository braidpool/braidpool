
In this post we describe a futures contracts between miners and market
makers that is enforced by the bitcoin blockchain. Miner and market
agree on a Exahash to BTC price on a fixed date (expiry date). On the
expiry date, the miner and the market maker execute an atomic trade to
exchange the hashrate (and any payouts earned) for BTC.

The protocol described depends on using braidpool hubs as DLC
oracles. There are two on-chain transactions required to execute the
contract once every contract period - one for the miner to get BTC
from market maker and the other for the market maker to get the
hashrate (and BTC) earned by the miner.

## Contracts Overview

There's two 2 of 2 multisig contracts:

1. The hub and miner setup a one-way payout rewards channel. This
   contract is funded entirely by the hub.
2. Market maker and the miner enter into a discrete log contract (DLC)
   with their chosen hubs acting as oracles. The miner "buys" this
   contract by jointly funding the contract with the market maker.

These two get tied together using an adaptor signature (tweaked public
key) from the miner:

1. The output of the DLC's "contract execution transaction" (CET) uses
   a tweaked public key from the miner. This tweaked key allows the
   market maker to spend the payout rewards channel output.
2. On contract expiry date, one or more hubs sign the DLC outcome,
   enabling the miner to spend their CET. This DLC outcome depends on
   the miner's hashrate as observed by the hubs.
3. The miner has to spend the CET to earn BTC for their hashrate. If
   the miner doesn't spend the CET, the market maker gets the miner's
   funds locked in the DLC.
4. As soon as the miner spends their CET, they reveal the secret key
   that allows the market maker to spend the output from the payout
   rewards channel.
   
At the end of the atomic trade, the market maker has the BTC that the
miner earned as payouts from the hub, and the miner can't double spend
the hash rate. The miner has the BTC proportional to their hashrate at
an agreed up exchange rate in the DLC contract.

## Details Coming Soon

We are currently working on a detailed description and will share it
with the wider community soon.
