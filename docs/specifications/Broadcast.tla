----------------------------- MODULE Broadcast -----------------------------
(*
The specification caputers the DAG base best effort broadcast to disseminate shares
over a peer to peer network.

First pass - We assume no processes failures or messages lost.  
*)

EXTENDS Naturals, Sequences

CONSTANT
            Proc,   \* Set of processes
            Data,
            Nbrs
             
VARIABLES
            sent,   \* Set of messages sent by processes to their neighbours
            recv    \* Set of messages received by processes
------------------------------------------------------------------------------
Message == [from: Proc, data: Data]

Init == 
        /\ sent = [m \in Message |-> {}]
        /\ recv = [m \in Message |-> {}]

TypeInvariant ==
        /\ sent \in [Message -> Proc]
        /\ recv \in [Message -> Proc]        
        
------------------------------------------------------------------------------

(*
Send(m, p) - send message m to neighbour q
*)
Send(m, p) == 
            /\ m.from # p
            /\ m.from \notin sent[m]
            /\ <<m.from, p>> \in Nbrs
            /\ sent' = [sent EXCEPT ![m] = @ \union {p}]
            /\ UNCHANGED <<recv>>

(*
Recv(m, q) - receive message m at q. This can be received from forwards
*)

Recv(m, q) == 
            /\ q \notin recv[m]
            /\ recv' = [recv EXCEPT ![m] = @ \union {q}]
            /\ UNCHANGED <<sent>>
        
(*
Forward(m, p, q) - forward message m from p to q
    - enabling condition - m has been sent by some process, q has received the message, q is not the sender
    - effect - p forwards the message m to its nbrs
*)

Forward(m, p, q) ==
            /\ p # q
            /\ <<p, q>> \in Nbrs
            /\ p \in recv[m]        \* p has received m
            /\ sent' = [sent EXCEPT ![m] = @ \union {q}]
            /\ UNCHANGED <<recv>>

Next == 
        \exists p \in Proc, q \in Proc, m \in Message: 
            \/ Send(m, p)
            \/ Recv(m, p)
            \/ Forward(m, p, q)
            
Spec == Init /\ [][Next]_<<sent, recv>>
-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Tue Mar 07 19:40:44 CET 2023 by kulpreet
\* Created Sun Mar 05 15:04:04 CET 2023 by kulpreet
