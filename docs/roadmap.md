# Version 0.0 (current)

1. Connects to other nodes via a command line option (no peer discovery)
2. Connects to bitcoind to receive block headers and transactions

# Version 0.1

The goal of the first version is to gather useful data about mining devices and expected particpants in Braidpool. We need to find out:

1. What is the latency in submitting a new work unit to a mining device?  In particular we need to *interrupt* any work the device thinks its doing and give it a new work unit. Braidpool beads will come in with a mean time between 150ms-1000ms, and we need to stop whatever the mining device is doing (if it hasn't found a solution) in a timeframe much less than that.
2. How large of a coinbase can the mining unit handle?  The Bitmain S5 famously killed P2Pool by restricting the size of the coinbase transaction. The entire coinbase transaction is handed to the mining device because in addition to the nonce field, the coinbase transaction also contains the "extranonce" field which the mining device rolls. But some mining pools like Eligus, Ocean, and P2Pool additionally paid miners in the coinbase resulting in very large coinbases that the S5 couldn't handle. Braidpool can pay miners in coinbases if it's viable. We need to determine its viability.
3. What is the network latency we can expect given our p2p system and the network realities of real miners.

During the 0.1 phase we will recruit miners to point **one** device of each type (manufacturer, bios version, batch number, etc) to the pool, and fill out a small form indicating what the mining device is, so that we can get a map of which mining devices *can* work with the low latencies that braidpool requires. We can use this to pressure mining device manufacturers to lower their latency and increase the size of their coinbase buffer. There's no technical reason why either of these should be limited, but anecdotal evidence indicates that both are limited on some hardware.

During this phase we want to acquire a diversity of devices (for the above measurements), as well as geographic diversity (for network latency measurements), but not hashrate. Please do not point multiple devices of the same type to the pool.

We will mine to the Braidpool donation address during this phase. If we win a block we will use it to fund developers, but we expect that the hashrate will be far too low for that and are not depending on funding in this manner. If you're so inclined the donation address is bcXXXXXX and we'd rather you donate than point more mining devices. Adding more mining devices decreases the probability that some odd hardware wins a share and decreases our ability to gather measurements about it.

Requirements:
1. Braid implementation (possibly use Kaspa's DAGKnight Rust implementation)
2. getblocktemplate from bitcoin
3. Stratum V2 integration (using their StratumV1 proxy to devices)
4. Docker images (or other runnable image solution)
5. Manual peer discovery via command line

# Version 0.2

1. Peer discovery mechanism (DHT or other)
2. Testnet version available, keep mainnet "donation" running, continue to solicit hashrate from new devices
3. Expansion of p2p system to include block and tx relay

# Version 0.3

1. Implementation of "slots" key-value store to keep track of FROST signers
2. Implementation of share validation checks (full block checks with txs)

# Version 0.4

1. Implementation of difficulty adjustment algorithm, with user selected difficulty (software will provide a recommended difficulty given the number of mining devices it sees to keep a constant variance among miners regardless of their size)
2. Initial implentation of FROST signing using "slots"

# Version 0.5

1. Public launch of Braidpool. You will be able to actually mine on it with payouts every 2 weeks. UX will be command line and shit but we will provide Docker images.
2. Miner monitoring console (UX) initial implementation

# Version 0.6

1. Initial implementation of transaction system (sending of shares). We will probably straight up copy bitcoin using libconsensus or similar. 

# Version 0.7

1. P2P latency improvements through Forward Error Correction over UDP (FEC).
2. Polish that UX

# Version 0.8

1. Initial implementation of "sub-pools". (Braidpool that mines into parent Braidpool) to decrease the smallest possible miner by 1000x.

# Version 0.9

1. Everything I forgot in the above

# Version 1.0

To the moon!
