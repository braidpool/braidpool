-------------------------- MODULE P2PBroadcastSpec --------------------------
(***************************************************************************)
(* Spec for a reliable p2p broadcast.                                      *)
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
(* Message is a record including the sending proc and a data               *)
(***************************************************************************)
Message == [from: Proc, data: Data]

Init == /\ sent = {}
        /\ received_by = [m \in Message |-> {}]

TypeOK ==   /\ sent \in SUBSET Message
            /\ received_by \in [Message -> SUBSET Proc]
------------------------------------------------------------------------------

(***************************************************************************)
(* Send message m                                                         *)
(***************************************************************************)
Send(m) ==  /\ m \notin sent            \* Message is sent only once by the original sender
            /\ sent' = sent \cup {m}    
            /\ UNCHANGED <<received_by>>

(***************************************************************************)
(* Receive a message m at proc p                                           *)
(***************************************************************************)
Recv(m, p) ==   /\ m \in sent                   \* receive only if m was sent first
                /\ p \notin received_by[m]      \* receive only once
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

(***************************************************************************)
(* Liveness is a temporal property that captures the property that if a    *)
(* message is sent, it is eventually received.                             *)
(*                                                                         *)
(* The WF Conjuction rule is used here ref: Specifying Systems p 105       *)
(***************************************************************************)

Liveness == \exists m \in Message, p \in Proc: WF_vars(Send(m) \/ Recv(m, p))
=============================================================================
\* Modification History
\* Last modified Sat Apr 08 21:02:35 CEST 2023 by kulpreet
\* Created Wed Apr 05 09:47:12 CEST 2023 by kulpreet
