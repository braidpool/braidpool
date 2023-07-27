----------------------------- MODULE BlockGeneration -------------------------
(***************************************************************************)
(* Block generation specifies when and how braidpool miners generate       *)
(* blocks.                                                                 *)
(* Block generation captures how coinbase and UHPO transactions are        *)
(* or updated.                                                             *)
(* The protocol to build current pool key and threshold signatures is      *)
(* assumed                                                                 *)
(***************************************************************************)

EXTENDS
        TLC,
        Sequences,
        Integers,
        DAG,
        FiniteSets

CONSTANT
        Miner,                   \* Set of miners
        ShareSeqNo,              \* Share seq numbers each miner generates
        BlockReward,             \* Block reward in a difficulty period
        GenesisShare

VARIABLES
        \* TODO: Replace these `last_.* variables with operators on DAG
        last_sent,               \* Function mapping miner to last sent share seq_no
        share_dag,              \* A DAG with valid shares for now implemented as a set
        stable,                 \* Set of shares that are stable in the DAG, i.e. received
                                \* by all other miners
        unpaid_coinbases,       \* coinbases for braidpool blocks that
                                \* haven't been paid yet
        uhpo,                   \* Function mapping miner to unpaid balance
        pool_key,               \* Current public key for TS
        chain                   \* chain of bitcoin blocks

-----------------------------------------------------------------------------

(***************************************************************************)
(* Share is a record of miner and sequence number.                         *)
(* All shares are assumed to be mined at same difficulty                   *)
(***************************************************************************)
Share == [miner: Miner, seq_no: ShareSeqNo]

(***************************************************************************)
(* PublicKey is defined as the set of miner identifiers for now.           *)
(* As miners join/leave the network, the public key immediately changes    *)
(* The protocol to rotate the threshold signature public key is not speced *)
(* here.                                                                   *)
(***************************************************************************)
\* PublicKey == Miner

(***************************************************************************)
(* Coinbase is a payment to a DKG public key with an value.                *)
(***************************************************************************)
CoinbaseOutput == [scriptPubKey: Miner, value: BlockReward]

CoinbaseTx == [inputs: <<>>, outputs: <<CoinbaseOutput>>]
                        
-----------------------------------------------------------------------------
NoVal == 0

Init ==
        /\ last_sent = [m \in Miner |-> IF m = GenesisShare.miner THEN 1 ELSE NoVal]
        /\ share_dag = [node |-> {GenesisShare}, edge |-> {}]
        /\ stable = {}
        /\ unpaid_coinbases = {}
        /\ uhpo = [m \in Miner |-> {}]
        /\ pool_key = {GenesisShare.miner}
        /\ chain = <<GenesisShare>>

TypeInvariant ==
        /\ last_sent \in [Miner -> Int \cup {NoVal}]
        /\ share_dag.node \in SUBSET Share
        /\ share_dag.edge \in SUBSET (Share \times Share)
        /\ stable \in SUBSET Share
        /\ unpaid_coinbases \in SUBSET CoinbaseOutput
        /\ uhpo \in [Miner -> SUBSET Share]
        /\ pool_key \in SUBSET Miner
        /\ chain \in Seq(Share)

vars == <<last_sent, share_dag, stable, unpaid_coinbases, uhpo, pool_key, chain>>
-----------------------------------------------------------------------------

(***************************************************************************)
(* Send a share from a miner with a seqno = last share sent + 1 and in     *)
(* ShareSeqNo.                                                             *)
(* The share is assumed to be successfully broadcast to all miners.        *)
(***************************************************************************)
SendShare(m, sno) ==
            /\ sno = last_sent[m] + 1
            /\ last_sent' = [last_sent EXCEPT ![m] = @ + 1]
            /\ share_dag' = [share_dag EXCEPT
                                \* Add share to node list of graph
                                !.node = @ \cup {[miner |-> m, seq_no |-> sno]},
                                \* Add edge from share to all non NoVal last_sent
                                \* This can be replaced by last share in DAG from others
                                !.edge = @ \cup
                                    {[miner |-> m, seq_no |-> sno]}
                                    \times
                                    {[miner |-> mo, seq_no |-> last_sent[mo]]:
                                          mo \in {mm \in Miner: last_sent[mm] # NoVal}}]
            /\ UNCHANGED <<stable, unpaid_coinbases, uhpo, pool_key, chain>>

(***************************************************************************)
(* Stabilise a share if there is a path from the share to any share from   *)
(* all other miners.                                                       *)
(*                                                                         *)
(* How do we know all other miners? This comes from a separate protocol    *)
(* where a miner is  dropped from the set of all other miners.             *)
(*                                                                         *)
(* Miners are dropped from the list if they have not sent shares since the *)
(* last bitcoin block was found. For now, we assume the list of to the     *)
(* group of miners is known.                                               *)
(***************************************************************************)
StabiliseShare(s) ==
                    /\ s \notin stable
                    /\ \A m \in Miner \ {s.miner}:
                        \exists p \in SimplePath(share_dag),
                                      i \in 1..Cardinality(share_dag.node),
                                      j \in 1..Cardinality(share_dag.node):
                                        /\ Len(p) > 1 
                                        /\ i < j
                                        /\ j =< Len(p)
                                        /\ p[i].miner = s.miner
                                        /\ p[j].miner = m
                    /\ stable' = stable \cup {s}
                    /\ UNCHANGED <<last_sent, share_dag, unpaid_coinbases, uhpo, pool_key, chain>>

(*
On receiving a bitcoin block miners create a new new bitcoin block 
they are mining on.

Miners have to create a new coinbase transaction. However, the UHPO 
transaction remains the same.
*)
\* ReceiveBitcoinBlock ==

(*
A miner on braidpool finds a new bitcoin block
1. Include the miner in the pool_key
2. Update UHPO payout miners and amount

Some miners can send shares with the old block
*)
FoundBitcoinBlock(share) == 
            /\ last_sent[share.miner] = share.seq_no
            /\ \A i \in 1..Len(chain): chain[i] # share
            /\ chain' = Append(chain, share)
            /\ pool_key' = pool_key \cup {share.miner}
            /\ \A ss \in NodesInSimplePath(share_dag,
                                   chain[Len(chain)],
                                   chain[1]):
                       uhpo' = [uhpo EXCEPT ![ss.miner] = @ \union {ss}]
            /\ UNCHANGED <<stable, last_sent, share_dag, unpaid_coinbases>>

-----------------------------------------------------------------------------
Next ==
        \/ \exists s \in Share: 
                \/ SendShare(s.miner, s.seq_no)
                \/ StabiliseShare(s)
                \/ FoundBitcoinBlock(s) \* Any share can be a bitcoin block.
                                        \* We do not model difficulty or track valid bitcoin flag.

Liveness == \A s \in share_dag.node: WF_vars(StabiliseShare(s) \/ FoundBitcoinBlock(s))

Spec ==
        /\ Init
        /\ [][Next]_vars
        
FairSpec == Spec
            /\ Liveness
=============================================================================
