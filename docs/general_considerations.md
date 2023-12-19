I'm writing this post to help organize and clarify some of the thought
surrounding "decentralized mining pools" for bitcoin, their requirements, and
some unsolved problems that must be solved before such a thing can be fully
specified.

# Decentralized Mining Pools for Bitcoin

A decentralized mining pool consists of the following components:
1. A [weak block](#weak-blocks) and difficulty target mechanism,
2. A [consensus mechanism](#consensus-mechanism) for collecting and accounting
   for shares,
3. A [payout commitment](#payout-commitment) requiring a quorum of participants
   to sign off on share payments,
4. A [signing procedure](#signing-procedure) for signing the [payout
   commitment](#payout-commitment) in such a way that the pool participants are
   properly paid,
5. A [transaction selection](#transaction-selection) mechanism for building
   valid bitcoin blocks.

The improvements being made by the
[StratumV2](https://github.com/stratum-mining/sv2-spec) project also include
encrypted communication to mining devices. These problems are important largely
factorizable from the pool itself, so we won't include discussion of that here,
but it is assumed that any decentralized mining pool would use the StratumV2
communications mechanisms.

# Weak Blocks

A *share* is a "weak block" that is defined as a standard bitcoin block that
does not meet bitcoin's target difficulty $T$, but does meet some lesser
difficulty target $t$. The *pool* specifies this parameter $t$ and when "weak
block" is found, it is communicated to the pool.

The share is itself a bearer proof that a certain amount of sha256 computation
has been done. The share itself must have a structure that indicates that it
"belongs" to a particular pool. In the case of centralized pools, this happens
because the pool itself hands out "work units" (bitcoin headers) corresponding
to a block that has been created by the pool, with transaction selection done
by the (centralized) pool.

In the case of a decentralized pool, the share itself must have additional
structure that indicates to other miners in the pool that the share belongs to
the pool, and if it had met bitcoin's difficulty target, the share contains
commitments such that all *other* miners in the pool would be paid according to
the share tally achieved by the decentralized [consensus
mechanism](#consensus-mechanism) of the pool.

Shares or blocks which do not commit to the additional metadata proving that the
share is part of the pool must be excluded from the share calculation, and those
miners are not "part of" the pool. In other words, submitting a random sha256
header to a pool must not count as a share contribution unless the ultimate
payout for that share, had it become a bitcoin block, would have paid the pool
in such a way that all other hashers are paid.

For example, consider a decentralized mining pool's "share" that looks like:

    Version | Previous Block Hash | Merkle Root | Timestamp | Difficulty Target | Nonce
    Coinbase Transaction | Merkle Sibling | Merkle Sibling | ...
    Pool Metadata

Here the `Merkle Siblings` in the second line are the additional nodes in the
transaction Merkle tree necessary to verify that the specified `Coinbase
Transaction` transaction is included in the `Merkle Root`. We assume that this
`Coinbase Transaction` commits to any additional data needed for the pool's
[consensus mechansim](#consensus-mechanism), for instance in an `OP_RETURN`
output.

The `Coinbase Transaction` is a standard transaction having no inputs, and
should have the following outputs:

    OutPoint(Value:0, scriptPubKey OP_RETURN <Pool Commitment>)
    OutPoint(Value:<block reward>, scriptPubKey <P2TR pool_pubkey>)

The `<block reward>` is the sum of all fees and block reward for this halving
epoch, and `pool_pubkey` is an address controlled collaboratively by the pool in
such a way that the [consensus mechanism](#consensus-mechanism) can only spend
it in such a way as to pay all hashers in the manner described by its share
accounting.

The `<Pool Commitment>` is a hash of `Pool Metadata` committing to any
additional data required for the operation of the pool. At a minimum, this must
include the weak difficulty target $t$ (or it must be computable from this
metadata). Validation of this share requires that the PoW hash of this bitcoin
header be less than this weak difficulty target $t$.

Other things that one might want to include in the `<Pool Commitment>` are:

1. Pubkeys of the hasher that can be used in collaboratively signing the
    [payout commitment](#payout-commitment),
2. Keys necessary for encrypted communication with this miner,
3. Identifying information such as an IP address, TOR address, or other routing
   information that would allow other miners to communicate out-of-band with
   this miner
4. Parents of this share (bead, in the case of braidpool), or other
   consensus-specific data if some other [consensus
   mechansim](#consensus-mechanism) is used.
5. Intermediate consensus data involved in multi-round threshold signing
   ceremonies.

Finally we note that there exists a proposal for [mining coordination using
covenants (CTV)](https://utxos.org/uses/miningpools/) that does not use weak
blocks, does not sample hashrate any faster than bitcoin blocks, and is
incapable of reducing variance. It is therefore not a "pool" in the usual sense
and we will not consider that design further, though covenants may still be
useful for a decentralized mining pool, which we discuss in [Payout
Commitments](#payout-commitments).

# Consensus Mechanism

In a centralized pool, the central pool operator receives all shares and does
accounting on them. While this accounting is simple, the point of a
decentralized mining pool is that we don't want to trust any single entity to do
this correctly, nor do we want to give any single entity control to steal all
funds in the pool, or the power to issue payments incorrectly.

Because of this, all hashers must receive the [shares](#weak-blocks) of all
other hashers. Each share could have been a bitcoin block if it had met
bitcoin's difficulty target and must commit to the pool metadata as described
above.

With the set of shares for a given epoch, we must place a consensus mechanism on
the shares, so that all participants of the pool agree that these are valid
shares and deserve to be paid out according to the pool's payout mechanism.

The consensus mechanism must have the characteristic that it operates much
*faster* than bitcoin, so that it can collect as many valid shares as possible
between valid bitcoin blocks. The reason for this is that one of the primary
goals of a pool is *variance reduction*.
[P2Pool](https://en.bitcoin.it/wiki/P2Pool) achieved this by using a standard
blockchain having a block time of 30s, and the [Monero
p2pool](https://github.com/SChernykh/p2pool) achieves it using a block time of
10s.

Bitcoin has spawned a great amount of research into consensus algorithms which
might be considered here including the [GHOST
protocol](https://eprint.iacr.org/2013/881), [asynchronous
PBFT](https://eprint.iacr.org/2016/199), "sampling" algorithms such as
[Avalanche](https://arxiv.org/abs/1906.08936) and that used by
[DFinity](https://arxiv.org/abs/1704.02397), and
[DAG-based](https://eprint.iacr.org/2018/104) algorithms. (This is not an
exhaustive bibliography but just a representative sample of the options)

One characteristic that is common to all consensus algorithms is that consensus
cannot be arrived at faster than roughly the global network latency. Regardless
of which consensus algorithm is chosen, it is necessary for all participants to
see all data going into the current state, and be able to agree that this is the
correct current state. Surveying the networks developed with the above
algorithms, one finds that the fastest they can come to consensus is in around
one second. Therefore the exact "time-to-consensus" of different algorithms
varies by an O(1) constant, all of them are around 1 second. This is around 600
times faster than bitcoin blocks, and results in miners 600 times smaller being
able to contribute, and a 600x factor reduction in variance compared to solo
mining.

While a 600x decrease in variance is a worthy goal, this is not enough of an
improvement to allow a single modern mining device to reduce its variance enough
to be worthwhile. Therefore, a different solution must be found for miners
smaller than a certain hashrate. We present some ideas in
[Sub-Pools](#sub-pools).

From our perspective, the obvious choice for a consensus algorithm is a DAG
which re-uses bitcoin's proof of work in the same spirit as bitcoin itself --
that is, the chain tip is defined by the heaviest work-weighted tip, and
conflict resolution within the DAG uses work-weighting. Note that this is the
same as the "longest chain rule" which only works at constant difficulty, but we
assume the DAG does not have constant difficulty so combining difficulties must
be done correctly. The solution is to identify the heaviest weight linear path
from genesis to tip, where the difficulties are summed along the path.

Finally, we caution that in considering mechanisms to include even smaller
miners, one must not violate the "progress-free" characteristic of bitcoin. That
is, one should not sum work from a subset of smaller miners to arrive at a
higher-work block in the DAG.

# Payout Commitment

The Payout Commitment is the coinbase output on bitcoin, containing all funds
from the block reward and fees in this block. This payout must commit to the
share payout structure as calculated at the time the block is mined.  In other
words, it must represent and commit to the consensus of the decentralized mining
pool's share accounting.

Validating the output of the [consensus mechanism](#consensus-mechanism) is well
beyond the capability of bitcoin script. Therefore generally one must find a
mechanism such that a supermajority (Byzantine Fault Tolerant subset) of
braidpool participants can sign the output, which is essentially reflecting the
consensus about share payments into bitcoin.

## The Unspent Hasher Payment Output (UHPO) mechanism

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
across two different difficulty adjustment windows $d_1$ and $d_2$. Shares in one difficulty
adjustment window have a different value $BTC_1$ compared to shares in another window $BTC_2$,
due to the difficulty adjustment itself. If one can compute the discrete derivative

$$
    \frac{d({\rm hashrate})}{d({\rm BTC})} = \frac{d_1-d_2}{BTC_1 - BTC_2}
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
