----------------------------- MODULE BlockGeneration -------------------------
(***************************************************************************)
(* Block generation specifies when and how braidpool miners generate       *)
(* blocks.                                                                 *)
(* The protocol to build current pool key and threshold signatures is      *)
(* assumed                                                                 *)
(***************************************************************************)

EXTENDS
        Sequences,
        Integers,
        DAG,
        FiniteSets

CONSTANT
        Miner,                   \* Set of miners
        ShareSeqNo,              \* Share seq numbers each miner generates
        BlockReward,             \* Block reward in a difficulty period
        MaxPathLen               \* Max path length to check for message stability.
                                 \* This helps constrain the search space in the DAG.

VARIABLES
        \* TODO: Replace these `last_.* variables with operators on DAG
        last_sent,               \* Function mapping miner to last sent share seq_no
        share_dag,              \* A DAG with valid shares for now implemented as a set
        stable,                 \* Set of shares that are stable in the DAG, i.e. received
                                \* by all other miners
        unpaid_coinbases,       \* coinbases for braidpool blocks that
                                \* haven't been paid yet
        uhpo,                   \* Function mapping miner to unpaid balance
        pool_key                \* Current public key for TS

-----------------------------------------------------------------------------

(***************************************************************************)
(* Share is a record of miner and sequence number.                         *)
(* All shares are assumed to be mined at same difficulty                   *)
(***************************************************************************)
Share == [miner: Miner, seq_no: ShareSeqNo]

(***************************************************************************)
(* Acks are the implicit acknowledgements sent with each share.  These are *)
(* the sequence number of shares receieved from each miner.                *)
(***************************************************************************)
Acks  == <<Share>>

(***************************************************************************)
(* PublicKey is defined as sequence of miner identifier for now.           *)
(* The miners in a key sequence are the miners contributing to the key     *)
(* generated using DKG.                                                    *)
(***************************************************************************)
PublicKey == Seq(Miner)

(***************************************************************************)
(* Coinbase is a payment to a DKG public key with an value.                *)
(***************************************************************************)
Coinbase == [key: PublicKey, value: BlockReward]
                        
-----------------------------------------------------------------------------
NoVal == 0

Init ==
        /\ last_sent = [m \in Miner |-> NoVal]
        /\ share_dag = [node |-> {}, edge |-> {}]
        /\ stable = {}
        /\ unpaid_coinbases = {}
        /\ uhpo = [m \in Miner |-> NoVal]
        /\ pool_key = <<>>

TypeInvariant ==
        /\ last_sent \in [Miner -> Int \cup {NoVal}]
        /\ share_dag.node \in SUBSET Share
        /\ share_dag.edge \in SUBSET (Share \times Share)
        /\ stable \in SUBSET Share
        /\ unpaid_coinbases \in SUBSET Coinbase
        /\ uhpo \in [Miner -> Int \cup {NoVal}]
        /\ pool_key \in Seq(Miner)

vars == <<last_sent, share_dag, stable, unpaid_coinbases, uhpo, pool_key>>
-----------------------------------------------------------------------------

(***************************************************************************)
(* Send a share from a miner with a seqno = last share sent + 1 and in     *)
(* ShareSeqNo.                                                             *)
(* The share is assumed to be successfully broadcast to all miners.        *)
(***************************************************************************)
SendShare == \exists m \in Miner, sno \in ShareSeqNo:
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
            /\ UNCHANGED <<stable, unpaid_coinbases, uhpo, pool_key>>

(*
Stabilise a share if there is a path from the share to any share from all other miners.
How do we know all other miners? This comes from a separate protocol where a miner is 
dropped from the set of all other miners. Miners are dropped from the list if they have
not sent shares since the last bitcoin block was found. For now, we assume the list of
to the group of miners is known. 
*)
StabiliseShare == \exists s \in share_dag.node:
                    /\ s \notin stable
                    /\ \A m \in Miner \ {s.miner}:
                        \exists p \in Paths(MaxPathLen, share_dag): /\ p[1].miner = m
                                                                    /\ p[2].miner = s.miner
                    /\ stable' = stable \cup {s}
                    /\ UNCHANGED <<last_sent, share_dag, unpaid_coinbases, uhpo, pool_key>>

DAGConstraint == Cardinality(share_dag.node) <= Cardinality(Miner) * Cardinality(ShareSeqNo)

\* RecvBitcoinBlock

\* FindBitcoinBlock

\* UpdatePoolKey

-----------------------------------------------------------------------------
Next ==
        \/ SendShare
        \/ StabiliseShare

Spec ==
        /\ Init
        /\ [][Next]_vars
=============================================================================
