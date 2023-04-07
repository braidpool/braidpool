-------------------------- MODULE P2PBroadcastSpec --------------------------
(***************************************************************************)
(* Spec for a reliable broadcast.                                          *)
(* This captures the                                                       *)
(* requirement that if any processor sends a message then eventually all   *)
(* other processes receive the message.                                    *)
(***************************************************************************)

EXTENDS Naturals, Sequences, FiniteSets

CONSTANT
            Proc,   \* Set of processes
            Data
VARIABLES
            sent,      \* All messages sent by all processors
            received_by   \* All messges received. Function from message to receiving processors
------------------------------------------------------------------------------
vars == <<sent, received_by>>

(***************************************************************************)
(* Message is a record including the sending proc and a data.              *)
(***************************************************************************)
Message == [from: Proc, data: Data]

Init == /\ sent = {}
        /\ received_by = [m \in Message |-> {}]

TypeOK ==   /\ sent \in SUBSET Message
            /\ received_by \in [Message -> SUBSET Proc]
------------------------------------------------------------------------------

(***************************************************************************)
(* Send message m.                                                         *)
(***************************************************************************)
Send(m) ==  /\ m \notin sent            \* Message is sent only once by the original sender
            /\ sent' = sent \cup {m}    
            /\ UNCHANGED <<received_by>>

(***************************************************************************)
(* Receive a message m at proc p                                           *)
(***************************************************************************)
Recv(m, p) ==   /\ m \in sent                   \* receive only if m was sent first
                /\ p \notin received_by[m]      \* receieve only once
                /\ received_by' = [received_by EXCEPT ![m] = @ \cup {p}]
                /\ UNCHANGED <<sent>>

Next == \exists m \in Message, p \in Proc: Send(m) \/ Recv(m, p)
------------------------------------------------------------------------------
Spec == Init /\ [][Next]_vars
------------------------------------------------------------------------------
(***************************************************************************)
(* FairSpec is Spec with the addition requirement that it keeps taking     *)
(* steps.                                                                  *)
(***************************************************************************)
FairSpec == Spec /\ WF_vars(Next)
=============================================================================
\* Modification History
\* Last modified Fri Apr 07 08:46:38 CEST 2023 by kulpreet
\* Created Wed Apr 05 09:47:12 CEST 2023 by kulpreet
