----------------------------- MODULE Broadcast -----------------------------
(*
The specification caputers the DAG base reliable broadcast to disseminate shares
over a peer to peer network.

The broadcast enables nodes to know which nodes have revceived the message by
using implicit acknowledgements. The broadcast is not a BFT broadcast. We depend
on the higher layers to provide that.

Does this open this broadcast to a DDoS attack? Yes, and our argument remains that
p2p network can resist DDoS attacks by other means.

First pass - We assume no processes failures or messages lost.  
*)

EXTENDS Naturals, Sequences

CONSTANT
            Proc,   \* Set of processes
            Data,
            Nbrs
             
VARIABLES
            sent_by,   \* Set of messages sent by processes to their neighbours
            recv_by    \* Set of messages received by processes
------------------------------------------------------------------------------
Message == [from: Proc, data: Data]

Init == 
        /\ sent_by = [m \in Message |-> {}]
        /\ recv_by = [m \in Message |-> {}]

TypeInvariant ==
        /\ sent_by \in [Message -> Proc]
        /\ recv_by \in [Message -> Proc]
        
------------------------------------------------------------------------------

(*
SendTo(m, p) - send message m to neighbour p

Sending to self is required as then the message is in the recv list as well.
*)
SendTo(m, p) ==
            /\ m.from \notin sent_by[m] \* Don't send again - we can add decay here
            /\ <<m.from, p>> \in Nbrs   \* Send only to neighbours
            /\ sent_by' = [sent_by EXCEPT ![m] = @ \union {p}]
            /\ UNCHANGED <<recv_by>>

(*
RecvAt(m, q) - receive message m at q. This can be received from forwards
*)

RecvAt(m, q) ==
            /\ \exists p \in Proc: p \in sent_by[m] \* Some process has sent the message
            /\ q \notin recv_by[m]                  \* Not already received by q
            /\ recv_by' = [recv_by EXCEPT ![m] = @ \union {q}]
            /\ UNCHANGED <<sent_by>>
        
(*
Forward(m, p, q) - forward message m from p to q
    - enabling condition - m has been sent by some process, q has received the message, q is not the sender
    - effect - p forwards the message m to its nbrs
*)

Forward(m, p, q) ==
            /\ \exists r \in Proc: r \in sent_by[m] \* Some process has sent the message
            /\ p # q                                \* Don't forward to self
            /\ <<p, q>> \in Nbrs                    \* Forward only to neighbour
            /\ p \in recv_by[m]                     \* p has received m
            /\ sent_by' = [sent_by EXCEPT ![m] = @ \union {q}]
            /\ UNCHANGED <<recv_by>>

Next == \exists p \in Proc, q \in Proc, m \in Message:
            \/ SendTo(m, p)
            \/ RecvAt(m, p)
            \/ Forward(m, p, q)
-----------------------------------------------------------------------------
Spec == /\ Init
        /\ [][Next]_<<sent_by, recv_by>>
-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Thu Mar 09 18:07:19 CET 2023 by kulpreet
\* Created Sun Mar 05 15:04:04 CET 2023 by kulpreet
