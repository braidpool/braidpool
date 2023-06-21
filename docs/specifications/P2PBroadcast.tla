----------------------------- MODULE P2PBroadcast -----------------------------
(***************************************************************************)
(* The specification caputers the DAG based reliable broadcast to          *)
(* disseminate messages over a peer to peer network.                       *)
(*                                                                         *)
(* The broadcast enables nodes to know which nodes have revceived the      *)
(* message by using implicit acknowledgements.  The broadcast is not a BFT *)
(* broadcast.  We depend on the higher layers to provide that.             *)
(*                                                                         *)
(* Does this open this broadcast to a DDoS attack? Yes, and our argument   *)
(* remains that p2p network can resist DDoS attacks by other means.        *)
(*                                                                         *)
(* We include a liveness propery that if a process sends a message         *)
(* then all processes received the message                                 *)
(***************************************************************************)

EXTENDS Naturals, Sequences

CONSTANT
            Proc,   \* Set of processes
            Data,
            Nbrs
             
VARIABLES
            channels,   \* All channels between nodes, can be indexed as
                        \* channels[from][to] and channels[to][from] and has a
                        \* queue of messages
            sent_by,    \* Function from message to all Proc that have sent it
            sent,       \* Same as P2PBroadcastSpec
            received_by \* Same as P2PBroadcastSpec

vars == <<sent_by, received_by, channels, sent>>
------------------------------------------------------------------------------
Message == [from: Proc, data: Data]

Init == 
        /\ sent_by = [m \in Message |-> {}]
        /\ received_by = [m \in Message |-> {}]
        /\ channels = [<<p, q>> \in Nbrs |-> <<>>]    \* Messages delivered in order
        /\ sent = {}

TypeInvariant ==
        /\ sent_by \in [Message -> SUBSET Proc]
        /\ received_by \in [Message -> SUBSET Proc]
        /\ channels \in [Nbrs -> Seq(Message)]
        /\ sent \in SUBSET Message

------------------------------------------------------------------------------

(***************************************************************************)
(* SendTo(m, p) - send message m to neighbour p                            *)
(*                                                                         *)
(* Sending to self is required as then the message is in the recv list as  *)
(* well.                                                                   *)
(***************************************************************************)
SendTo(m, p) ==
        /\ m.from \notin sent_by[m]                     \* Don't send again
        /\ <<m.from, p>> \in Nbrs                       \* Send only to neighbours
        /\ sent_by' = [sent_by EXCEPT ![m] = @ \union {m.from}]
        /\ sent' = sent \cup {m}
        /\ channels' = [channels EXCEPT ![<<m.from, p>>] = Append(@, m)]
        /\ UNCHANGED <<received_by>>

(***************************************************************************)
(* RecvAt(m, q) - receive message m at q.  This can be received from       *)
(* forwards                                                                *)
(***************************************************************************)

RecvAt(m, p, q) ==
            /\ <<p, q>> \in Nbrs                        \* receive only at neighbours
            /\ channels[<<p, q>>] # <<>>                \* receive if there is a message
            /\ m = Head(channels[<<p, q>>])             \* receive the message at head
            /\ \exists r \in Proc: r \in sent_by[m]     \* Some process has sent the message
            /\ q \notin received_by[m]                  \* Not already received by q
            /\ received_by' = [received_by EXCEPT ![m] = @ \union {q}]
            /\ channels' = [channels EXCEPT ![<<p, q>>] = Tail(@)]
            /\ UNCHANGED <<sent_by, sent>>

(***************************************************************************)
(* Lose message m on channel between processes p and q.                    *)
(***************************************************************************)
Lose(m, p, q) ==
            /\ <<p, q>> \in Nbrs
            /\ channels[<<p, q>>] # <<>>
            /\ m = Head(channels[<<p, q>>])
            /\ channels' = [channels EXCEPT ![<<p, q>>] = Tail(@)]
            /\ UNCHANGED <<sent, sent_by, received_by>>

(***************************************************************************)
(* Forward(m, p, q) - forward message m from p to q                        *)
(*                                                                         *)
(* Enabling condition - m has been sent by some process, q has received    *) 
(* the message, q is not the sender                                        *)
(*                                                                         *)
(* Effect - p forwards the message m to its nbrs                           *)
(***************************************************************************)

Forward(m, p, q) ==
            /\ \exists r \in Proc: r \in sent_by[m] \* Some process has sent the message
            /\ p # q                                \* Don't forward to self
            /\ m.from # p                           \* Sender does not forward
            /\ <<p, q>> \in Nbrs                    \* Forward only to neighbour
            /\ p \in received_by[m]                     \* p has received m
            /\ p \notin sent_by[m]                  \* Don't forward again
            /\ sent_by' = [sent_by EXCEPT ![m] = @ \union {p}]
            /\ channels' = [channels EXCEPT ![<<p, q>>] = Append(@, m)]
            /\ UNCHANGED <<received_by, sent>>

(***************************************************************************)
(* Track message received at so we can build a liveness property that      *)
(* sends lead to receive.                                                  *)
(***************************************************************************)
ReceivedAt(m, p) ==
        /\ m.from # p                               \* Receive at non-sender
        /\ p \in received_by[m]                     \* Message has been received by m
        /\ UNCHANGED vars

Next == \exists p \in Proc, q \in Proc, m \in Message:
            \/ SendTo(m, p)
            \/ RecvAt(m, p, q)
            \/ Lose(m, p, q)
            \/ Forward(m, p, q)
-----------------------------------------------------------------------------
Spec == /\ Init
        /\ [][Next]_vars


(***************************************************************************)
(* Sends leads to recv is a liveness property saying if a message is sent by *)
(* any process, then all processes eventually receive the message.         *)
(***************************************************************************)
SendLeadsToRecv == \A m \in Message: \A p, q \in Proc:
                WF_vars(ReceivedAt(m, q))

(***************************************************************************)
(* Liveness specifies that if a message is enabled to be received at p, it *)
(* is eventually received at p.                                            *)
(***************************************************************************)
Liveness == \A p, q \in Proc: \A m \in Message: WF_vars(RecvAt(m, p, q))

FairSpec == Spec
            /\ Liveness
            /\ SendLeadsToRecv
-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant

(*
This specification implements the P2PBroadcastSpec
*)
PBS == INSTANCE P2PBroadcastSpec
THEOREM Spec => PBS!Spec
=============================================================================
\* Modification History
\* Last modified Wed Jun 21 15:59:29 CEST 2023 by kulpreet
\* Created Sun Mar 05 15:04:04 CET 2023 by kulpreet
