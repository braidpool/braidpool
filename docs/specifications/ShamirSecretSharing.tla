------------------------ MODULE ShamirSecretSharing ------------------------
(***************************************************************************)
(* Sepcification for simple Shamir Secret Sharing. This is not a veriable  *)
(* secret sharing scheme.                                                  *)
(*                                                                         *)
(* We specify that dealer first sends shares to all players, and once all  *)
(* players have received their shares the can eventually reconstruct the   *)
(* secret.                                                                 *)
(*                                                                         *)
(* We do not deal with the communication protocol between players to send  *)
(* their shares to each other before reconstructing the secret.            *)
(*                                                                         *)
(* We use a trick from https://github.com/tlaplus/Examples/blob/master/specifications/ewd840/SyncTerminationDetection.tla *)
(* to detect that all players have reconstructed the secret and we have    *)
(* detected it                                                             *)
(***************************************************************************)

EXTENDS Integers, Sequences, Reals, TLC

CONSTANT
        Dealer,         \* The dealer sharing the secret with the players
        Players,        \* Set of all players
        Coefficients    \* The coefficient of the polynomial. These are provided by the model
        
VARIABLES
        shares,             \* Function mapping Player to computed shares
        shares_sent,        \* Function mapping Player to shares received
        shares_received,    \* Function mapping Player to received shares
        reconstructed,      \* Function mapping Player to flag if secret
                            \* has been successfully constructed
        allReconstructDetected          \* We detected all reconstructions
                                        \* and can therefore terminate 
        
vars == <<shares, shares_sent, shares_received, reconstructed, allReconstructDetected>>
-----------------------------------------------------------------------------
NoValue == -1

Init == 
        \* Compute shares as a + bx + cx^2
        /\ shares = [p \in Players |-> Coefficients[1] + Coefficients[2] * p + Coefficients[3] * p ^ 2]
        /\ shares_sent = [p \in Players |-> NoValue]
        /\ shares_received = [p \in Players |-> NoValue]
        /\ reconstructed = [p \in Players |-> FALSE]
        /\ allReconstructDetected = FALSE

(***************************************************************************)
(* The type invariant for all variables.                                   *)
(***************************************************************************)
TypeOK ==
        /\ shares \in [Players -> Int]
        /\ shares_sent \in [Players -> Int]
        /\ shares_received \in [Players -> Int]
        /\ reconstructed \in [Players -> BOOLEAN]
        /\ allReconstructDetected \in BOOLEAN
        
allReconstructed == \A p \in Players: reconstructed[p]
-----------------------------------------------------------------------------

(***************************************************************************)
(* Send the share to Player p.                                             *)
(***************************************************************************)
SendShare(p) ==
        /\ shares_sent[p] = NoValue
        \* Send a share that has not been sent to anyone
        /\ shares_sent' = [shares_sent EXCEPT ![p] = shares[p]]
        /\ UNCHANGED <<shares, shares_received, reconstructed, allReconstructDetected>>
        
(***************************************************************************)
(* Receive the share at Player p. It should have been sent before.         *)
(***************************************************************************)
ReceiveShare(p) ==
        /\ shares_received[p] = NoValue
        /\ shares_sent[p] # NoValue
        /\ shares_received' = [shares_received EXCEPT ![p] = shares_sent[p]]
        /\ UNCHANGED <<shares, shares_sent, reconstructed, allReconstructDetected>>
                
(***************************************************************************)
(* Reconstruct secret with Players p and q.                                *)
(* The payers should have receieved share.                                 *)
(***************************************************************************)
Reconstruct(p,q) ==
        /\ \A t \in Players: shares_received[t] # NoValue
        /\ p # q
        /\ shares_received[p] # NoValue
        /\ shares_received[q] # NoValue
        /\ reconstructed[p] = FALSE
        \* We don't specify how the secret is reconstructed, just that it is
        \* reconstructed using shares of all two player combinations
        /\ reconstructed' = [reconstructed EXCEPT ![p] = TRUE]
        /\ allReconstructDetected' \in {allReconstructDetected, allReconstructed'}
        /\ UNCHANGED <<shares, shares_sent, shares_received>>
        

DetectReconstructed ==
        /\ allReconstructed
        /\ allReconstructDetected' = TRUE
        /\ UNCHANGED <<shares, shares_sent, shares_received, reconstructed>>
  
  
-----------------------------------------------------------------------------
(***************************************************************************)
(* The next step either sends shares, receieves them or reconstructs the   *)
(* secret.                                                                 *)
(***************************************************************************)
Next == \exists p, q \in Players:
            \/ SendShare(p)
            \/ ReceiveShare(p)
            \/ Reconstruct(p, q)
            \/ DetectReconstructed
        
Spec == 
        /\ Init
        /\ [][Next]_vars

(***************************************************************************)
(* Liveness states that eventually all players reconstruct the secret.     *)
(***************************************************************************)
Liveness == \A p, q \in Players: 
        WF_vars(ReceiveShare(p) /\ Reconstruct(p, q) /\ DetectReconstructed)

(* Stability - once all reconstructions are detected, all Players' secrets *)
(* remain reconstructed.                                                   *)        
Stable == [](allReconstructDetected => []allReconstructed)

(***************************************************************************)
(* For a fair specification, we assure the spec takes next steps and       *)
(* liveness is guaranteed.                                                 *)
(***************************************************************************)
FairSpec == Spec /\ Liveness
=============================================================================
