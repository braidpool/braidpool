
# Braidpool Specification

Herein we present the specification for a decentralized mining pool we name
"Braidpool". For background information and general considerations please read
[General Considerations for Decentralized Mining
Pools](https://github.com/mcelrath/braidcoin/blob/master/general_considerations.md)
which has relevant general discussion omitted from this document.  The sections
below correspond to the sections in that document, describing how Braidpool will
solve each of the indicated issues.  Orthogonal considerations including
encrypted miner communication is being pursued by the
[StratumV2](https://github.com/stratum-mining/sv2-spec) project, which Braidpool
will build upon.

## Table of Contents

1. [Shares and Weak Blocks](#shares-and-weak-blocks)
    1. [Metadata Commitments](#metadata-commitments)
    2. [Share Value](#share-value)
2. [Braid Consensus Mechansim](#braid-consensus-mechanism)
    1. [Simple Sum of Descendant Work](#simple-sum-of-descendant-work)
    2. [Difficulty Retarget Algorithm](#difficulty-retarget-algorithm)
    3. [Miner-Selected Difficulty](#miner-selected-difficulty)
3. [Payout Update](#payout-commitment)
    1. [Unspent Hasher Payment Output](#unspent-hasher-payment-output)
4. [Payout Update and Settlement Signing](#payout-update-and-settlement-signing)
5. Transaction Selection

# Shares and Weak Blocks

A *share* is a "weak block" that is defined as a standard bitcoin block that
does not meet bitcoin's target difficulty $x_b$, but does meet some lesser
difficulty target $x$.

The share is itself a bearer proof that approximately $w=1/x$ sha256
computations have been done. The share data structure has additional data that
indicates to other miners that the share belongs to Braidpool, and if it had met
bitcoin's difficulty target, it contains commitments such that all *other*
miners in the pool would be paid according to the share tally.

Shares or blocks which do not commit to the additional metadata proving that the
share is part of the Braidpool must be excluded from the share calculation, and
those miners are not "part of" the pool. In other words, submitting a random
sha256 header to a Braidpool node must not count as a share contribution unless
the ultimate payout for that share, had it become a bitcoin block, would have
paid all members of the pool in such a way that all other hashers are paid.

A Braidpool "share" or "bead" is a data structure containing a bitcoin block
header, the coinbase transaction, and metadata:

| Field      | Description |
| ---------- | ----------- |
| `blockheader` | `Version, Previous Block Hash, Merkle Root, Timestamp, Target, Nonce` |
| `coinbase`    | `Coinbase Txn, Merkle Sibling, Merkle Sibling, ...` |
| `payout`      | `Payout Update Txn, Merkle Sibling, Merkle Sibling, ...` |
| `metadata`    | `Braidpool Metadata` (see below) |
| `un_metadata` | `Uncommitted Metadata` (see below) |

The first line is a standard Bitcoin block header.  The `Merkle Siblings` in the
second and third line are the additional nodes in the transaction Merkle tree
necessary to verify that the specified `Coinbase Transaction` and `Payout
Commitment` transactions are included in the `Merkle Root`. This `Coinbase
Transaction` commits to any additional data needed for the Braidpool's [braid
consensus mechansim](#braid-consensus-mechanism), in an `OP_RETURN` output.
While we could commit to this data in a more space-efficient manner (e.g. via a
pubkey tweak), the coinbase is also the location of the `extranonce` 8-byte
field used by some mining equipment.

The `Coinbase Transaction` is a standard transaction having no inputs, and
must have the following outputs:

    OutPoint(Value:0, scriptPubKey OP_RETURN "BP"+<Braidpool Commitment>+<extranonce>)
    OutPoint(Value:<block reward>, scriptPubKey <P2TR pool_pubkey>)

The `<block reward>` is the sum of all fees and block reward for this halving
epoch, and `pool_pubkey` is an address controlled collaboratively by the pool in
such a way that the [braid consensus mechanism](#braid-consensus-mechanism) can
only spend it in such a way as to pay all hashers in the manner described by its
share accounting.

## Metadata Commitments

The `<Braidpool Commitment>` is a hash of `Braidpool Metadata` committing to
additional data required for the operation of the pool. Validation of this share
requires that the PoW hash of this bitcoin header be less than this weak
difficulty target $x$.

The `Braidpool Metadata` is:
| Field           | Description                                                     |
| -----           | -----------                                                     |
| `target`        | Miner-selected target difficulty $x_b < x < x_0$                |
| `payout_pubkey` | P2TR pubkey for this miner's payout                             |
| `comm_pubkey`   | secp256k1 pubkey for encrypted DH communication with this miner |
| `miner IP`      | IP address of this miner                                        |
| [[`parent`, `timestamp`], ...] | An array of block hashes of parent beads and timestamps when those parents were seen |

The `Uncommitted Metadata` block is intentionally not committed to in the PoW
mining process. It contains:
| Field             | Description |
| -----             | ----------- |
| `timestamp`       | timestamp when this bead was broadcast |
| `signature`       | Signature on the `Uncommitted Metadata` block using the `payout_pubkey` |

The purpose of this data is to gather higher resolution timestamps than are
possible if the timestamp was committed. All Braidpool timestamps are 64-bit
fields as milliseconds since the Unix epoch. When a block header is sent to
mining devices, many manufacturers' mining devices do not return for quite some
time (10-60 seconds) while they compute the hash, which causes PoW-mined
timestamps to be delayed by this amount. Adding timestamps when parents were
seen by the node and a timestamp when the bead was broadcast allows the braid to
compute bead times with much higher precision. Though the data is uncommitted in
the PoW header, it is signed by a key that is committed in the PoW header, so
third parties cannot falsify these timestamps.

## Share Value

A great many [share payout
algorithms](https://medium.com/luxor/mining-pool-payment-methods-pps-vs-pplns-ac699f44149f)
have been proposed and used by pools. Because Braidpool will not collect fees
and has no source of funds other than block rewards with which pay hashers, it
will use the **Full Proportional** method, meaning that all rewards and fees are
fully distributed to hashers proportionally to their contributed shares. Closely
related methods like Pay Per Share (PPS) allow the pool operator to earn the
fees, but a decentralized mining pool has no operator which could/should be
earning these fees. While many projects have inserted a "developer donation", we
feel that Braidpool is an open source public good that should be developed and
maintained by the community, without the political drama of who and how to pay
with a source of funds.

With PPS-type methods, most centralized pool operators are taking a risk on
paying immediately for shares, therefore absorbing the variance risk involved in
"luck". For hashers that desire immediate payout this can be achieved using any
third party willing to buy their shares and take on the risk management of
"luck" and fee variance. It's not necessary or desirable for Braidpool itself to
subsume this risk management function. It is logical to allow professional risk
management firms to take it on by directly buying shares. We envision that
existing pools might run on top of Braidpool and continue to perform this risk
management function for their clients.

Other payout algorithms such as Pay Per Last N Shares (PPLNS) were created
primarily to discourage pool hopping. We don't feel that this is needed in the
modern day and a smoothing function applied to payouts interferes with the
notion of using shares as a hashrate derivative instrument.

A purely work-weighted proportional algorithm would work for a pure-DAG
blockchain, however we have the problem that some of the beads are blocks in a
parent blockchain, and the parent blockchain has the property that some blocks
can be orphans and receive no reward. We must dis-incentivize the creation of
blocks which might become orphans. One component of this solution is the
[difficulty retarget algorithm](#difficulty-retarget-algorithm) which maximizes
throughput while minimizing the number of simultaneous beads.

However simultaneous beads will happen naturally due to the faster bead time,
latency, and attackers. Within a time window $T_C$ (the cohort time), the
probability that 2 or more blocks is generated by the parent blockchain can be
obtained by summing the Poisson distribution in terms of its rate parameter
$\sigma$ (usually called $\lambda$) and is

$$
P_{\ge 2}(T_C) = \sum_{k=2}^\infty \frac{\sigma(T_C)^k e^{-\sigma(T_C)}}{k!} = 1 - e^{-\sigma(T_C)} (1+\sigma(T_C))
$$

where

$$
\sigma(T_C) = \frac{T_C}{\rm block\ time} \left(\frac{\rm pool\ hashrate}{\rm total
\ hashrate}\right)
$$

Therefore shares within a cohort containing 2 or more beads must be weighted by
$(1-P_{\ge 2}(T_C))$. Beads which are "blockchain-like" will be counted as full
shares, while beads in larger cohorts will be counted as slightly less than a
full share by this factor. The value $T_C$ is the cohort time, which is half the
time difference between the median of the parent cohort's timestamps, and the
median of the descendant cohort's timestamps. Here we use only the timestamps
as witnessed by descendants, not the claimed broadcast time by the miner in
`Uncommitted Metadata`.

(FIXME: Is it appropriate to apply this factor to even blockchain-like beads?)

As $T_C$ grows, the value of shares decreases. Therefore an attacker attempting
to reorganize transactions or execute a selfish mining attack will see the value
of his shares decrease in an appropriate way corresponding to how likely it is
that he generates an orphan and reduces the profit of the pool.

Summing it all up, the number of shares $s$ for a given bead is given by:

$$
s = \frac{1}{x (1-P_{\ge 2})}
$$

Where $x_b \le x \le x_0$ is the [miner-selected
difficulty](#miner-selected-difficulty), $x_0$ is the minimum target given by
the [Difficulty Retarget Algorithm](#difficulty-retarget-algorithm), and $x_b$
is the bitcoin target. Note that $w = 1/x$ is traditionally called the "work",
and is a statistical estimate of the number of sha256d computations performed by
the miner.

At first glance this algorithm might seem to "punish" lower-target (higher work)
miners given [miner-selected difficulty](#miner-selected-difficulty), however
because it is directly proportional to work $w=1/x$, it weights high-work miners
more than low-work miners. So while a low-work miner is more likely to generate
a multi-bead cohort with a high-work miner, the reward and share is
appropriately work-weighted.

The sum of shares generated by this formula must be equal to the actual work
going into the blockchain, minus work lost due to orphans (communications
latency).

# Braid Consensus Mechanism

The consensus algorithm we choose is inspired by simply extending Nakamoto
consensus to a Directed Acyclic Graph. We call nodes in this DAG "beads" and the
overall structure a "braid" so as to distinguish it from the bitcoin blocks and
chain. Some of the beads in the DAG are bitcoin blocks.

We call this structure a "braid" because it contains an extra restriction
relative to a general DAG: beads must not name as parents other beads which are
ancestors of another parent. Naming a parent that is an ancestor of another
parent conveys no useful information, since ancestors of each parent are already
implied when ordering the DAG and including transactions. Visually this means
that a braid will never have triangles or some other higher order structures.

A DAG can be totally ordered in linear time using either [Kahn's
algorithm](https://dl.acm.org/doi/10.1145/368996.369025) or a modified
depth-first search which terminates when a bead is found that is a common
ancestor to all of a bead's parents, which defines a "graph cut" and a point of
global consensus on all ancestors. We define the set of beads between two graph
cuts to be a "cohort". Within a cohort it is not possible to total order the
contained beads using graph structure alone. The cohort can be defined as a set
of beads having the same set of oldest common descendants and youngest common
ancestors.

It should be noted that within a braid we keep *all* beads with a valid PoW,
regardless of whether they are considered invalid in other ways, or contain
conflicting transactions. Transaction conflict resolution within the Braid is
decided by the [work weighting algorithm](#work-weighting-algorithm) and doing
so requires retaining both sides of the conflict. It is generally possible for
new work to change which beads are considered in the "main chain", just as in
Bitcoin new work can cause a reorganization of the chain ("reorg"), which makes
a block that was previously an orphan be in the main chain.

We have considered the [PHANTOM](https://eprint.iacr.org/2018/104) proposal
which has many similarities to ours and should be read by implementors. We
reject it for the following reasons:

1. The k-width heuristic is somewhat analogous to our cohorts, but has the
   property that it improperly penalizes naturally occurring beads. If for
   example we target the bead rate such that 40% of the cohorts have 2 or more
   beads, this means that approximately 2.5% of cohorts would have 4 or more
   beads. The red/blue algorithm of PHANTOM would improperly penalize all but
   the first three of the beads in this cohort.

2. It is impossible in practice to reliably identify "honest" and "attacking"
   nodes. There is only latency, which we can measure and take account of. Even
   in the absence of attackers, cohorts exceeding the k-width happen naturally
   and cannot be prevented.

## Simple Sum of Descendant Work

Within Bitcoin, the "Longest Chain Rule" determines which tip has the most work
among several possible tips. The "Longest Chain Rule" only works at constant
difficulty and the actual rule is a "Highest Work" rule when you consider
difficulty changes.

Therefore we require an algorithm to calculate the total work for each bead.
This total work can then be used to select the highest work tips as well as to
select transactions within beads which have more work than other beads for
transaction conflict resolution.

For conflict resolution, we choose the Simple Sum of Descendant Work (SSDW),
which is the sum of work among descendants for each bead, disregarding any graph
structure. This is the direct analog of Nakamoto's "longest chain/highest work"
rule.  Graph structure is manipulable at zero cost, therefore we must have a
conflict resolution algorithm that is independent of graph structure, lest we
create a game which can be played to give a non-work advantage to an attacking
miner which he could use to reverse transactions. The SSDW work is:

$$
    w_{\rm SSDW} = \sum_{i \in \rm descendants} \frac{1}{x_i}
$$

where $x_i$ is the target difficulty for descendant $i$, and $1/x$ is
traditionally called the "work".

The SSDW can be optimized by first applying the Cohort algorithm, since all
beads in a parent cohort have all beads in all descendant cohorts added to their
work. Therefore, the only thing that matters for conflict resolution is
descendant work *within* a cohort.

In the event that two beads containing conflicting transactions have exactly the
same SSDW, the one with the lower hash ("luck") will be selected.

## Difficulty Retarget Algorithm

![Cohort time $T(x)$ vs target difficulty $x$](https://github.com/mcelrath/braidcoin/raw/master/T_C_x.png)

The cohort time $T(x)$ in terms of the target difficulty $x$ is well
approximated (green line in above graph) by

$$
T(x) = \frac{1}{\lambda x} + a e^{a \lambda x}
$$

where $a$ is a latency parameter and $\lambda$ is a rate parameter given by

$$
a = T_C W\left(\frac{T_C}{T_B} - 1 \right); \qquad
\lambda = \frac{N_B}{x T_C N_C},
$$

where $T_B = \frac{1}{\lambda x}$ is the bead time, $T_C$ is the (measured)
cohort time, and $W(z)$ is the [Lambert W
function](https://en.wikipedia.org/wiki/Lambert_W_function).

Given a starting value for $x$, we can measure these parameters directly from
the braid within a time window corresponding to a retarget epoch:
| Parameter   | Description |
| ----------- | ----------- |
| $N_B$       | Number of beads   |
| $N_C$       | Number of cohorts |
| $T_C$       | Cohort time |
| $T_B$       | Bead time |

This function has a minimum at

$$
x_0 = \frac{2 W\left(\frac12\right)}{a \lambda} = \frac{0.7035}{a \lambda}.
$$

This minimum corresponds to the fastest possible cohort time, and the most
frequent global consensus achievable in a braid. For smaller target difficulty
$x \to 0$, the braid becomes blockchain-like, and
$T(x) \xrightarrow[x\rightarrow 0]{} (\lambda x)^{-1} + a + \mathcal{O}(x)$,
showing that the parameter a is the increase in effective block time due to
network latency effects. In the opposite limit $x \to \infty$, cohorts become
large, meaning that beads cannot be total ordered, double-spend conflicts cannot
be resolved, and global consensus is never achieved. In this limit the cohort
time increases exponentially, so we cannot let $x$ get too large.

This gives us a zero-parameter retargeting algorithm. At any time we can
evaluate $x_0$, which represents a maximum target difficulty that the braid will
accept.

[Braid Retargeting
Algorithm](https://rawgit.com/mcelrath/braidcoin/master/Braid%2BExamples.html)
contains the full analysis that results in this formula including code to
reproduce this result.

## Miner Selected Difficulty

Within the Braid we wish to allow different miners to select their difficulty
and to target for constant *variance* among miners by allowing a small miner to
use a lower difficulty than a larger miner. Miners may select any difficulty
between the maximum target $x_0$ described in [Difficulty Retarget
Algorithm](#difficulty-retarget-algorithm) and the bitcoin target.

Braidpool will automatically select an appropriate target difficulty based on
the miner's observed hashrate. Larger miners will see a higher target selected
while smaller miners will see a lower target, where we will seek that each miner
is expected to produce on average one bead per bitcoin block. For miners smaller
than this they will be allocated to a [Sub-Pool](#sub-pools).

Note that this equal-variance target is not enforceable by consensus. A miner
could choose to run multiple Braidpool instances or just change the code to
select a different target, and the Braidpool software-selected target is an
unenforceable recommendation. The consequence of a miner ignoring this
recommendation would be to decrease a single miner's variance at the expense of
producing more beads in the braid for the same amount of work. This slows down
the braid and increases the bead time. Accepting this equal-variance target
allows Braidpool to accommodate the maximum number of miners, the most work, and
the fastest possible bead time without resorting to allocating more miners to
[Sub-Pools](#sub-pools).

# Payout Update

The Payout Update is a separate transaction from the coinbase transaction
that aggregates previous coinbase outputs into a single new output. This output
contains all funds from the block reward and fees in this and all past blocks.
This payout must commit to the share payout structure as calculated at the time
the block is mined.  In other words, it must represent and commit to the
consensus of the decentralized mining pool's share accounting. This transaction
has two inputs and one output

    Input (1): <existing Braidpool payout update UTXO>
    Input (2): <block N-100 coinbase output>
    Outputs (1): <new Braidpool payout update UTXO>

Validating the output of the [consensus mechanism](#consensus-mechanism) is well
beyond the capability of bitcoin script. Therefore generally one must find a
mechanism such that a supermajority (Byzantine Fault Tolerant subset) of
Braidpool participants can sign the output, which is essentially reflecting the
consensus about share payments into bitcoin. This is done by having a single
P2TR public key which is controlled by a Byzantine fault tolerant supermajority
of miners which must cooperate to sign the output.

The payout is a rolling commitment that spends the previous payout update
output and creates a new one including rewards and fees from the new block. This
must be signed with `SIGHASH_ANYONECANPAY` so that the output amount is
uncommitted in the sighash. Since each miner may choose different transactions,
the exact amount of the fee reward in this block cannot be known until a block
is successfully mined, and we cannot commit to this value.

Since newly created coinbase outputs cannot be spent for 100 blocks due to a
bitcoin consensus rule, the Payout Update transaction is always 100 blocks
in arrears. The transaction that must be included in a bead spends the most
recent Braidpool coinbase that's at least 100 blocks old into a new Payout
Commitment output.

![On-Chain Eltoo from the Eltoo paper](https://github.com/mcelrath/braidcoin/raw/master/eltoo.png)

This rolling set of payout updates is an on-chain version of the [Eltoo
protocol](https://blockstream.com/eltoo.pdf). By spending the previous Payout
Update, we automatically invalidate the previous UHPO payout tree, and replace
it with a new one. Old UHPO settlement transactions can no longer be broadcast
as they would be double-spends. Relative to the Eltoo diagram above, $T_{u,i}$
are Payout Commitment outputs, and $T_{s,i}$ are UHPO payout transactions.

Note that the most common discussions around Eltoo revolve around holding the
update transactions off-chain using a NOINPUT or ANYPREVOUT flag. In our case,
there is really no good reason to hold these updates off-chain nor wait for
these transaction flags to be deployed. These update transactions must be held
by Braidpool nodes between the time that they are signed and mined into a
block.

## Unspent Hasher Payment Output

For the payout commitment we present a new and simple record accounting for
shares. Consider the consensus mechanism as a UTXO-based blockchain analagous to
bitcoin. The "UTXO set" of the consensus mechanism is the set of payment outputs
for all hashers, with amounts decided by the recorded shares and consensus
mechanism rules.

We will term the set of hasher payments the Unspent Hasher Payment Output (UHPO)
set. This is the "UTXO set" of the decentralized mining pool, and calculation
and management of the UHPO set is the primary objective of the decentralized
mining pool.

The UHPO set can be simply represented as a transaction which has as inputs all
unspent coinbases mined by the pool, and one output for each unique miner with
an amount decided by his share contributions subject to the consensus mechanism
rules.

In p2pool this UHPO set was placed directly in the coinbase of every block,
resulting in a large number of very small payments to hashers. One advantage of
traditional pools is that the *aggregate* these payments over multiple blocks so
that the number of withdrawals per hasher is reduced. A decentralized mining
pool should do the same. The consequence of this was that in p2pool, the large
coinbase with small outputs competed for block space with fee-paying
transactions.

The commitment to the UHPO set in the coinbase output is a mechanism that allows
all hashers to be correctly paid if the decentralized mining pool shuts down or
fails after this block. As such, the UHPO set transaction(s) must be properly
formed, fully signed and valid bitcoin transactions that can be broadcast. See
[Payout Authorization](#payout-authorization) for considerations on how to
sign/authorize this UHPO transaction.

We don't ever want to actually have to broadcast this UHPO set transaction
except in the case of pool failure. Similar to other optimistic protocols like
Lightning, we will withhold this transaction from bitcoin and update it
out-of-band with respect to bitcoin. With each new block we will update the UHPO
set transaction to account for any new shares since the last block mined by the
pool.

Furthermore a decentralized mining pool should support "withdrawal" by hashers.
This would take the form of a special message or transaction sent to the pool
(and agreed by consensus within the pool) to *remove* a hasher's output from the
UHPO set transaction, and create a new separate transaction which pays that
hasher, [authorizes](#payout-authorization) it, and broadcasts it to bitcoin.
Miners may not cash out for the *current* difficulty adjustment window (because
the share/BTC price is not yet decided), but may only cash out for the *last*
(and older) difficulty adjustment window(s).

The share value for the *current* difficulty adjustment epoch is encoded
proportionally in the UHPO transactions, however this is only for use in the
case of catastrophic failure of Braidpool. During normal operation, the UHPO
transaction is fixed at the end of the difficulty adjustment window when the
share/BTC price for that epoch is known.

# Payout Update and Settlement Signing

Once a bitcoin block is mined by the pool, Braidpool will kick off a signing
ceremony to create a new Payout Commitment and UHPO settlement transaction.

It is impossible or impractical to sign the payout update and UHPO set
transactions prior to mining a block, because the extranonce used by mining
devices changes the coinbase txid, we can't sign this transaction until its
Input(2) txid is known.

After the RCA transaction is signed, and its corresponding UHPO transaction is
signed, spending the RCA's output, Braidpool nodes will *delete* the
corresponding key shares and keys associated with signing these. As long as
$n-t$ nodes successfully delete these shares and keys, and the RCA and UHPO
transactions are distributed to all nodes, it then becomes impossible to spend
the aggregated Braidpool funds in any other way.

FIXME should update and settlement keys be different here?

FIXME use a tapscript for the UHPO payment. Happy path is RCA, and just a
Schnorr signature.

FIXME Can we authorize the tapscript UHPO in any other way? Can we verify a PoW
hash for instance?

FIXME pre-kegen and ROAST parallel signing

FIXME use nlocktime or CSV? CSV would separate the update and settlement
transactions.

FIXME what do we do with any coinbases mined by Braidpool after the settlement
tx is broadcast? CSV and let the miner take it all?

FIXME from eltoo paper: "The use of different key-pairs prevents an attacker
from simply swapping out the branch selection and reusing the same signatures
for the other branch."
    This should still be possible with tapscript. An attacker can know the
    pubkey tweak and adapt an update signature to be a settlement signature and
    v/v.  (CHECK THIS)

The script

## Pool Transactions and Derivative Instruments

If the decentralized mining pool supports transactions of its own, one could
"send shares" to another party. This operation replaces one party's address in
the UHPO set transaction with that of another party. In this way unpaid shares
can be delivered to an exchange, market maker, or OTC desk in exchange for
immediate payment (over Lightning, for example) or as part of a derivatives
contract.

The reason that delivery of shares can constitute a derivative contract is that
they are actually a measurement of *hashrate* and have not yet settled to
bitcoin. While we can compute the UHPO set at any point and convert that to
bitcoin outputs given the amount of bitcoin currently mined by the pool, there
remains uncertainty as to how many more blocks the pool will mine before
settlement is requested, and how many fees those blocks will have.

A private arrangement can be created where one party *buys future shares* from
another in exchange for bitcoin up front. This is a *futures* contract, where
the counterparty to the miner is taking on pool "luck" risk and fee rate risk.

In order to form hashrate derivatives, it must be posible to deliver shares
across two different difficulty adjustment windows. Shares in one difficulty
adjustment window have a different value compared to shares in another window,
due to the difficulty adjustment itself. If one can compute the derivative

$$
    \frac{d({\rm hashrate})}{d({\rm BTC})} = \frac{d_1-d_2}{{\rm BTC}_1 - {\rm BTC}_2}
$$

then derivative instruments such as options and futures can be constructed by
private contract, where shares from different difficulty adjustment epochs are
delivered to the derivative contract counterparty in exchange for BTC, possibly
with time restrictions. We do not describe further how to achieve this, here we
are only pointing out that the sufficient condition for the decentralized mining
pool to support private contract derivative instruments are:

1. The ability to send shares to another party
2. The ability to settle shares into BTC at a well defined point in time with
   respect to the difficulty adjustment (for instance after the adjustment, for
   the previous epoch)
3. The ability transact shares across two difficulty adjustment windows.

It may be tempting to turn a decentralized mining pool into a full DeFi market
place with an order book. We caution that the problem of Miner Extractable Value
(MEV) is a serious one that destroys fairness and confidence in the system, and
should be avoided here. The only operations we consider here are (a) sending
shares to another party and (b) requesting payout in BTC for shares.

Finally let us note that the value of a "share" is naturally fixed after each
difficulty adjustment. Within one two-week difficulty adjustment window, each
sha256d hash attempt has a fixed value in terms of BTC, but the exact amount of
BTC is unknown until the next difficulty adjustment. Therefore, the 2-week
difficulty adjustment window is a natural point to automatically broadcast the
UHPO tree for the last epoch and settle out all shares from the previous epoch.

# Payout Authorization

In [Payout Commitment](#payout-commitment) we described a simple mechansim to
represent shares and share payouts as decided by the [Consensus
Mechansim](#consensus-mechansim) on shares at any point in time.  However,
bitcoin is incapable of evaluating the logic of the pool's consensus mechanism
and we must find a simpler way to represent that share payout consensus to
bitcoin, such that the coinbase outputs cannot be spent in any other way than as
decided by the pool's consensus.

Probably the most straightforward way to authorize the share payouts and signing
of coinbase outputs is to use a large threshold multi-signature. The set of
signers can be any pool participant running the pool's consensus mechanism and
having availability of all data to see that consensus mechanism's chain tip. We
assume that in the [weak block](#weak-blocks) metadata, the pool participants
include a pubkey with which they will collaboratively sign the payout
authorization.

FIXME -- choose a subset of nodes who submitted shares using a hash function to
"elect" them. Those nodes must then submit proof that their shares were valid by
broadcasting the transaction tree in their share. If validation fails, the
miner's shares are invalidated. This allows us to spot-check all hashers,
mitigate block withholding attacks, and keep the signing subset small.

The most logical set of signers to authorize the coinbase spends are the set of
miners who have already successfully mined a bitcoin block. We want to avoid
having any single miner having unilateral control over a coinbase and the
ability to steal the funds without paying other hashers. As such the minimum
number of signers is four, using the $(3f+1)$ rule from the Byzantine agreement
literature. This means that on pool startup, the first 4 blocks must be directly
and immediately paid out to hashers, as there are not enough known parties to
sign a multi-signature, and we don't even know their pubkeys to construct a
(P2TR, P2SH, etc) bitcoin output address and scriptPubKey.

After the first 4 blocks, we assume that 66%+1 miners who have previously mined
a block must sign the coinbase output(s), paying into the UHPO set transaction.

This is probably the biggest unsolved problem in building a decentralized mining
pool -- how to coordinate a large number of signers. If we assume that shares
are paid out onto bitcoin with every difficulty adjustment, this is 2016 blocks
and up to 1345 signers that must collaborate to make a threshold
multi-signature. This is a very large number and generally well beyond the
capabilities of available signing algorithms such as
[FROST](https://eprint.iacr.org/2020/852),
[ROAST](https://eprint.iacr.org/2022/550),
[MP-ECDSA](https://eprint.iacr.org/2017/552), or [Lindell's threshold
Schnorr](https://eprint.iacr.org/2022/374)
algorithm.

Below we discuss threshold Schnorr in more detail, but this may not be the only
way to commit to and then authorize spending of coinbases into the UHPO tree. We
encourage readers to find alternative solutions to this problem. The very large
drawback to all signing algorithms we are able to find is that they are
intolerant to failures.

## Schnorr Threshold Signatures

We have reviewed a large amount of literature on threshold Schnorr algorithms.

They all generally involve a Distributed Key Generation (DKG) phase using a
variant of [Pedersen's
DKG](https://link.springer.com/chapter/10.1007/3-540-46766-1_9), often
augmenting it with polynomial commitments introduced by Feldman to achieve a
[Verifiable Secret Sharing scheme
(VSS)](https://ieeexplore.ieee.org/document/4568297). There are many papers with
variations on this idea, each focusing on organizing rounds of communication,
assumptions about communication (such as whether a broadcast channel exists) and
security proofs.

Participants in the threshold signature each contribute entropy in the DKG phase
by creating and secret sharing their contribution to all other participants. In
this way a key can be created with entropy input from all participants, such
that no participant knows the key, but at the end of the DKG, all participants
hold shares of it such that a t-of-n threshold number of shares must be Lagrange
interpolated to reconstruct the secret.

These secret shares are then used to compute a signature. Instead of directly
reconstructing the secret key (which would give unilateral spending control to
the party doing the reconstruction) one computes the signature using the
secret share as the private key, and then Lagrange interpolation is performed on
the resulting set of signatures instead.

Both ECDSA and Schnorr signatures require a nonce $k$ which must additionally be
agreed upon by the signing participants before signing, and is committed to in
the signature itself. This is generally done by running an additional round of
the DKG to compute $k$ such that everyone has a secret share of it.

### Distributed Key Generation

# Transaction Selection

The [Stratum V2](https://github.com/stratum-mining/sv2-spec) project is focusing
on a model where hashers are responsible for constructing the block and
selecting transactions. This is an improvement over Stratum V1 where the
(centralized) pool chooses the block and transactions.

The risk here is that the pool either censors valid transactions at the
direction of a government entity, or prioritizes transactions through
out-of-band payment, risking the "censorship resistant" property of the system.

In the [Weak Blocks](#weak-blocks) section we did not indicate how transaction
selection was done. This is a factorizable problem, and for a decentralized
mining pool we also assume that individual hashers are constructing blocks, and
the pool places no further restrictions on the transaction content of a block
mined by a participating hasher. In fact, for weak blocks which do not meet
bitcoin's difficulty threshold, it is probably best to elide the transaction set
entirely for faster verification of shares. This introduces a problem that a
hasher could construct a block with invalid transactions, but this would be
easily discovered if that hasher ever mined a block, and his shares could
invalidated.

A transaction selection mechanism using both a decentralized mining pool and
Stratum V2 should be able to easily slot into the block structure required by
the decentralized mining pool as indicated in [weak blocks](#weak-blocks), as
long as Stratum V2 is tolerant of the required coinbase and metadata structure.

In our opinion simply allowing hashers to do transaction selection is
insufficient, as centralized pools can simply withhold payment unless hashers
select transactions according to the rules dictated by the pool. A full solution
that restores bitcoin's censorship resistance requires decentralized payment as
well.

# Attacks

## Block Withholding

## Coinbase Theft by Large Miners

Because signing very large threshold Schnorr outputs is impractical, it is
necessary to keep the number of signers $n$ of the t-of-n UHPO root output
relatively small, so as to complete the signature in a reasonable amount of time
and without consuming too much bandwidth or computation.

Therefore there exists the possibility that just due to luck, the same (large)
miner might mine all $n$ of the most recent blocks, or that two miners who
together mine all $n$ of the most recent blocks collude. In this case

The UHPO root must be signed by t-of-n of the most recent *distinct* miners
who successfully mined bitcoin blocks.

We might also consider including hashers who have not won bitcoin blocks. In
order to do this we might select a random subset of recent shares, and require
that those hashers prove the entire bitcoin block committed to in their share.
Upon successful validation of their share, they are included in the signing
subset for future blocks. Consensus on this signing subset would be included in
beads.

If a hasher is elected for UHPO signing, fails to provide proof of his

# Unsolved Problems and Future Directions

The largest unsolved problem here is that of the [Payout
Authorization](#payout-authorization). While off-the-shelf algorithms are
available such as [ROAST](https://eprint.iacr.org/2022/550), they require fixing
the set of signers and are intolerant to failure in either the nonce generation
phase, the signing phase, or both. A threshold number of participants must be
chosen, and must *all* remain online through the keygen and signing phase. If
any participant fails, a different subset must be chosen and the process
restarted. There does exist an [approach due to Joshi et
al](https://link.springer.com/chapter/10.1007/978-3-031-08896-4_4) at the cost
of an extra preprocessing step, which makes the final signature aggregation
asynchronous assuming the nonce generation was successful, though the setup
phases are still intolerant to failure.

The fact that both ECDSA and Schnorr signatures require a nonce $k$ is a big
drawback requiring an additional keygen round with everyone online that other
systems such as BLS do not have.

In practice if no new algorithm is found and an existing Schnorr threshold
signature is used (something involving a DKG and Shamir sharing), a balance must
be struck between having so many signers that payouts cannot be signed in a
reasonable time, and so few signers that the system is insecure and coinbases
could be stolen by a small subset.

An approach that might be considered is to sub-sample the set of signers, and
somehow aggregate signatures from subsets. As the resultant signatures would
have different nonces, they cannot be straightforwardly aggregated, but this is
the same problem as aggregating different signatures within a transaction or
block, and approaches to [Cross Input Signature Aggregation
(CISA)](https://github.com/ElementsProject/cross-input-aggregation) might be
used here and might indicate the desirability of a future soft fork in this
direction.

## Covenants

One might take the UHPO set transaction and convtert it to a tree structure,
using covenants to enforce the structure of the tree in descendant transactions.
This is often done in the context of covenant-based soft fork proposals so that
one party can execute his withdrawal while not having to force everyone else to
withdraw at the same time.

Because a decentralized mining pool is an active online system, it seems better
to use an interactive method to write a new transaction for a withdrawal, than
to allow broadcasting part of a tree. If part of a tree were broadcast, this
must also be noticed by all miners and the share payouts updated.

In our opinion the only reason the whole UHPO set transaction(s) would be
broadcast is in a failure mode or shutdown of the pool, in which case the tree
just increases the on-chain data load for no benefit.

## Sub-Pools

Since a consensus system cannot achieve consensus faster than the global
latency, this is an improvement in share size of at most about 1000x. In order
to support even smaller hashers, one might consider "chaining" the decentralized
mining pool to create a sub-pool.

Instead of coinbase UTXOs as inputs to its UHPO set, a sub-pool would have UHPO
set entries from a parent pool as entries in its UHPO set. With a separate
consensus mechanism from its parent, a chain of two decentralized mining pools
could allow hashers 1000000x smaller to participate. A pool could in principle
dynamically create and destroy sub-pools, moving miners between the sub-pools
and main pool dependent on their observed hashrate, so as to target a constant
variance for all hashers.


