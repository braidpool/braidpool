----------------------------- MODULE P2PChannel -----------------------------
(***************************************************************************)
(* Specify a channel between two nodes in a p2p network.                   *)
(*                                                                         *)
(* Messages can be sent multiple times on a channel.                       *)
(*                                                                         *)
(* Messages can be lost in a channel.                                      *)
(*                                                                         *)
(***************************************************************************)

EXTENDS Naturals, Sequence
CONSTANT Data
VARIABLE chan

TypeInvariant == 
        /\ chan \in [msgs: Seq(Data)]
-----------------------------------------------------------------------------

Init == /\ TypeInvariant
        /\ chan.msgs = <<>>
        
Send(d) ==  /\ Append(chan.msgs, d)

Recv    ==  /\ chan' = [chan EXCEPT !.msgs = Tail(@)]

Lose    ==  /\ chan' = [chan EXCEPT !.msgs = Tail(@)]

Next    ==  \/ (\exists d \in Data: Send(d))
            \/ Recv
            \/ Lose

Spec    == Init /\ [][Next]_chan
-----------------------------------------------------------------------------
THEOREM Spec => []TypeInvariant
=============================================================================
\* Modification History
\* Last modified Wed Mar 29 12:48:31 CEST 2023 by kulpreet
\* Created Wed Mar 29 12:19:34 CEST 2023 by kulpreet
