# What is Braidpool?

Braidpool is a decentralized mining pool for bitcoin. It is a short-lived Directed Acyclic Graph (DAG)-based layer-1 blockchain solely for the purpose of producing bitcoin blocks. It decentralizes *share accounting* and *payout*, in addition to transaction selection.

# Why?

Bitcoin's long block time (10 minutes) introduces revenue variance for miners that can only be overcome by being a larger and larger miner. For this reason Mining Pools have come into existence to pool hashrate from different miners to reduce their variance. This directly impacts the decentralization of the bitcoin network since pools want to maximize their hashrate to minimize their variance, but cannot get bigger than 51% or they are perceived as an attack risk on Bitcoin. A centralized pool "looks like" an individual miner with respect to the Bitcoin network.

Braidpool aims to decouple the problems of transaction selection, variance reduction, device monitoring, and mining payout in order to enhance the businesses of both pools and individual miners.

# What does Braidpool mean for existing pools?

Existing pools can run *on top* of Braidpool at no cost to them (Braidpool will be zero-fee) and we encourage them to do so. Doing this allows pools to decouple themselves from two unwinnable games:

**Variance reduction**:
    Pools can only reduce revenue variance by being big, but being big makes them an attack risk to a decentralized network, and a single point of control for hostile governments. The 51% attack risk still exists but is transferred to Braidpool itself. By having many miners acting individually in Braidpool instead of the pool appearing as one big miner, the risk of a 51% is substantially reduced. It would be safer if all miners operated on top of Braidpool, as long as no single miner has more than 51% of the hashrate. It's also safe for a buyer of shares to buy more than 51% of the shares without becoming a risk to decentralization.

**Transaction selection**:
    Pools are commonly accused of censoring transactions and constantly fight a PR battle over it. By leaving this responsibility to individual miners, transaction selection is decentralized. Block template construction is not outsourced as it is on Ethereum, which has resulted in more centralization around MEV-boosting traders and "compliant" blocks which are antithetical to Bitcoin.

**By running on top of Braidpool, pools can get out of the above unwinnable games and focus on the other aspects of their business:**

**Buying shares**:
    Existing centralized pools buy shares in exchange for Bitcoin. Because Braidpool only pays out every 2 weeks, pools can offer miners a faster payout method by buying their shares in exchange for BTC on-chain or in Lightning channels. This is technically a [Forward Contract](https://www.investopedia.com/terms/f/forwardcontract.asp). More complex instruments such as options can be built on top of it, and enable on the Braidpool chain by the ability to send your shares to the address of your pool counterparty. Braidpool is not a Decentralized Exchange and this kind of trading will have to happen privately, on existing exchanges, or over-the-counter (OTC) and is outside the scope of Braidpool.

**Risk Management**:
    Pools take a risk-on position with respect to the number of blocks the pool will win and the fees in those blocks. This is a duty taken on by hedge funds and market makers in other industries, and is accompanied by careful analysis of on-chain usage and expected changes in hashrate due to new mining devices or new facilities coming online. Miners outsource this responsibility in the [PPS model](https://medium.com/luxor/why-should-you-choose-a-pps-pool-5a71ee574478) and pools can continue to provide this service by running on Braidpool without creating a 51% attack risk. The PPS model requires a source of funds on the part of the pool and pools are not simply aggregators but are a financial counterparty. Diversifying this responsibility allows pools to specalize into legal jurisdictions while recognizing the financial nature of this part of their business.

**Device Monitoring**:
    Many miners use their pool for device monitoring. Because individual mining devices make direct connections to the pool, the pool can identify underperforming or non-functional mining devices, allowing the miner to take action. Pools also report site-wide hashrate and luck statistics so that operators can monitor their operation.

**Payment Routing**:
    By decoupling mining from share payout itself, it encourages pools to diversify their services by offering new technical means for miners to receive their payment, including the Lightning network, and future in-progress proposals like Ark, FediMint, and Mercury Layer. This would allow todays centralized pools to become the routing nodes of the future payment system we all want Bitcoin to become, earning fees by routing off-chain payments in addition to mining revenue.

# What does Braidpool mean for miners?

Miners can continue to use the pools they have existing relationships with (assuming their pool runs on Braidpool) for the reasons above. They will have to run the Braidpool node software and a Bitcoin full node. Braidpool will provide Docker images to make this as easy as possible since we know this is somewhat of a hurdle, but we believe this technical hurdle is easier to solve than the variance reduction and tx selection problems existing pools have.

Miners can choose to run on top of Braidpool directly. The payout algorithm is **Full Proportional** meaning over a single difficulty adjustment window (2016 blocks -- about 2 weeks), all funds (both block rewards and all fees) mined by Braidpool are paid out to miners in proportion to the shares they submitted to the pool. The choice of paying over an entire difficulty adjustment window is intended to avoid arbitrary "smoothing" that happens in PPLNS pools, while providing a definitive hashprice for each difficulty epoch that can be traded to create risk-management tools (financial derivatives). It is also chosen so that rewards are *aggregated* over a sufficient time period so that Braidpool does not create huge coinbase transactions like Eligus, Ocean and P2Pool, which competes with fee revenue. For instance one could buy shares in one epoch and sell shares in the upcoming epoch through private agreement, in order to create a hashrate derivative instrument.

Miners will have the ability to emulate their current PPS arrangement with pools by engaging a counterparty to buy their shares at a fixed price. Your counterparty will of course demand a fee or spread for this service, as they are taking on risk to do this, but we anticipate this fee will match current pool fees, and Braidpool itself does not impose additional fees. This will incentivize private parties to offer new financial and technical instruments, such as streaming payments over Lightning, and more complex and comprehensive contract arrangements.

An example of a more comprehensive contract that could be created would be a long-term share buying agreement at a fixed price. The repayment period for mining hardware is generally 6-18 months. Miners would really like to lock-in their risk until the hardware is paid off by buying a contract to send all their shares to their counterparty for a fixed price, allowing their counterparty to take on the risk of fee and hashrate variance. This is similar to the options and futures contracts used in agriculture and other commodities. Producers lock-in their price, mitigating the variance in crop yield and oil usage due to winter temperatures. Braidpool will enable this, with a diversity of risk-taking counterparties in your jurisdiction.

# A Few Technical Details

Braidpool is a Directed Acyclic Graph (DAG) of "beads" rather than a blockchain of "blocks". All this really means is that each bead can have multiple parents, and the graph can have diamonds or other higher-order graph structures within it. This is done to overcome the orphan/stale block problem in Bitcoin, while enabling much faster bead times (we estimate about 1000x faster).

These beads are "shares" and every time a miner wins one he adds an entry into the decentralized share accounting ledger that is Braidpool's UTXO set. Every bead could be a bitcoin full bitcoin block had it met Bitcoin's difficulty target, but Braidpool has a dynamic difficulty target that is around 1000x easier to hit, resulting in 1000 times more beads than Bitcoin blocks. At the end of the 2016-block difficulty window, all shares are automatically paid out according to the consensus rules of Braidpool, which enforce the Full Proportional payout algorithm.

Each bead has an associated value corresponding to the estimate of the number of sha256d hashes performed, commonly known as the [difficulty](https://en.bitcoin.it/wiki/Difficulty). This quantity has units of number of hashes performed and a miner's share of the total payout over one difficulty adjustment epoch is the sum of the difficulty of all the shares he found, relative to the sum of difficulty for all shares found by the pool. Therefore the share-coin, as a transferrable asset is difficulty, which settles out to Bitcoin on-chain at the end of the difficulty adjustment epoch.

Custody of accumulated coinbase rewards and fees is performed by a large multi-sig among miners who have recently mined blocks using the [FROST Schnorr signature algorithm](https://glossary.blockstream.com/frost/). Consensus rules on the network ensure that only a payout properly paying all miners can be signed and no individual miner or small group of colluding miners can steal the rewards.

# Current Status and How To Contribute

Braidpool is a nascent project written in Rust. We have published a [spec](https://github.com/braidpool/braidpool/blob/main/docs/braidpool_spec.md), and code which connects to peers and bitcoind. If any of the above features excite you, it's a great project to get in on the ground floor of a brand new blockchain that is *not* a shitcoin. No premine, no ICO, no BS, and with real utility.

More detailed specifications can be found in the [Braidpool
Spec](https://github.com/braidpool/braidpool/blob/master/docs/braidpool_spec.md)
which should be regarded as a work-in-progress.

If you want to chat about Braidpool, [join us on
Matrix](https://matrix.to/#/#braidpool:matrix.org)
