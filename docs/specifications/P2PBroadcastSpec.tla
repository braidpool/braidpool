-------------------------- MODULE P2PBroadcastSpec --------------------------
(***************************************************************************)
(* Spec for a reliable broadcast.                                          *)
(* This captures the                                                       *)
(* requirement that if any processor sends a message then eventually all   *)
(* other processes receive the message.                                    *)
(***************************************************************************)

EXTENDS Naturals, Sequences

CONSTANT
            Proc,   \* Set of processes
            Data
VARIABLES
            sent,      \* All messages sent
            received   \* All messges received
------------------------------------------------------------------------------
vars == <<sent, received>>

Message == [from: Proc, data: Data]

Init == /\ sent = <<>>
        /\ received = [m \in Message |-> {}]

TypeOK ==   /\ sent \in Seq(Message)
            /\ received \in [Message -> SUBSET Proc]
------------------------------------------------------------------------------
Send == /\ \exists m \in Message: sent' = Append(sent, m) \* Always enabled
        /\ UNCHANGED <<received>>

Recv(m) ==  /\ sent # <<>>
            /\ m = Head(sent)
            /\ sent' = Tail(sent)
            /\ \exists p \in Proc: received' = [received EXCEPT ![m] = @ \cup {p}]

Next == \exists m \in Message: Send \/ Recv(m)
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
\* Last modified Wed Apr 05 12:19:39 CEST 2023 by kulpreet
\* Created Wed Apr 05 09:47:12 CEST 2023 by kulpreet
