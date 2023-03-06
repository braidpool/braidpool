----------------------------- MODULE Broadcast -----------------------------
(*
The specification caputers the DAG base best effort broadcast to disseminate shares
over a peer to peer network.

First pass - We assume no processes failures or messages lost.  
*)

EXTENDS Naturals, Sequences

CONSTANT
            Proc  \* Set of processes
             
VARIABLES
            sent, \* Set of messages sent by all processes
            recv, \* Set of messages received by all processes
            acks  \* Set of acknowledgments for messages

Message == [op: {"send"}, from: Proc, seqNo: Nat] 
            \cup [op: {"recv"}, from: Proc, seqNo: Nat]

(*
Initially, no messages have been sent, receieved or acknowledged.
*)
INIT == 
        /\ sent = <<>>    
        /\ recv = [m \in Message |-> {}]   
        /\ acks = [m \in Message |-> {}] 

(*
Type invariant. 

sent is a sequence of messages
recv is a function from Message to procs that have receieved the message
acks is a function from Message to procs that have implicity acked it
*)
TypeInvariant == 
        /\ sent \in Seq(Message)
        /\ recv \in [Message -> Proc]
        /\ acks \in [Message -> Proc]

=============================================================================
\* Modification History
\* Last modified Mon Mar 06 09:07:56 CET 2023 by kulpreet
\* Created Sun Mar 05 15:04:04 CET 2023 by kulpreet
