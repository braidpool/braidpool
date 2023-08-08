---------------------- MODULE Bitcoin ----------------------
(***************************************************************************)
(* Specifies the behaviour of the bitcoin blockchain and transactions      *)
(***************************************************************************)

EXTENDS Sequences, Naturals, FiniteSets, TLC

CONSTANTS TxID,
          InputSeqNo,
          Amount,
          ScriptPubKey,     \* Script for outputs
          ScriptSig         \* Script for inputs
          
VARIABLES
          transactions     \* Set of all transactions

(***************************************************************************)
(* Input for a transaction has an id, sequence number and a scriptPubKey   *)
(***************************************************************************)
Input       == [txid: TxID, seqno: InputSeqNo, scriptPubKey: ScriptPubKey]

(***************************************************************************)
(* Output for a transaction has a scriptSig and an amount                  *)
(***************************************************************************)
Output      == [scriptSig: ScriptSig, amount: Amount]

(***************************************************************************)
(* Transaction is a set of inputs and outputs.                             *)
(*                                                                         *)
(* It is a coinbase transaction if inputs are empty.                       *)
(***************************************************************************)
\* Transaction == [id: TxID, inputs: SUBSET Input, outputs: SUBSET Output]

vars == <<transactions>>
-----------------------------------------------------------------------------

NoInputVal == CHOOSE v: v \notin Input

GenesisTransaction == [
                        id |-> CHOOSE x \in TxID: TRUE,
                        inputs |-> {},
                        outputs |-> {[scriptSig |-> CHOOSE x \in ScriptSig: TRUE,
                                      amount |-> CHOOSE amt \in Amount: TRUE]}
                       ]

Init == 
    /\ transactions = {GenesisTransaction}
    
TypeInvariant ==
    /\ \A tx \in transactions:
            \* Input can be empty for coinbases
            /\ tx.inputs \in SUBSET Input
            /\ tx.outputs \in SUBSET Output

(***************************************************************************)
(* An output is spendable if it is not market spent.                       *)
(***************************************************************************)
IsSpendableOutput(output) ==
        \* output doesn't appear in any existing transactions
        /\ output \notin UNION{tx.outputs : tx \in transactions}
        
(***************************************************************************)
(* Input exists in transactions and appears only once                      *)
(***************************************************************************)
ExistingInput(input) ==
        \/ transactions = {GenesisTransaction}
        \/ Cardinality({tx \in transactions: 
                            /\ tx.id = input.txid
                            /\ input \in tx.inputs}) = 1

(***************************************************************************)
(* Does the output scriptSig match the input scriptPubKey                  *)
(* For now, we are working with strings being equal. There is no           *)
(* scripting support.                                                      *)
(***************************************************************************)        
ScriptMatch(output, input) ==
        /\ output.scriptSig = input.scriptPubKey

(***************************************************************************)
(* Create a new transaction and add it immediately to the set of           *)
(* transactions.                                                           *)
(*                                                                         *)
(* Mark output as spent by the given input                                 *)
(*                                                                         *)
(* We don't spec block creation, broadcast of txs and                      *)
(* blocks or coinbase txs                                                  *)
(***************************************************************************)      
GenerateTransaction(txid, output, input) ==
        /\ ExistingInput(input)
        /\ txid \notin {tx.id : tx \in transactions}
        /\ IsSpendableOutput(output)
        /\ ScriptMatch(output, input)
        /\ transactions' = transactions \cup 
                                  {[id |-> txid,
                                    inputs |-> {input},
                                    outputs |-> {output}]}

-----------------------------------------------------------------------------

Next == 
    \/ \exists output \in Output, input \in Input, txid \in TxID:
        \/ GenerateTransaction(txid, output, input)
    
Spec == Init /\ [][Next]_vars

\* Safety

\* AllOutputsAreSpent
\* AllSpendScriptsMatch

\* Liveness
\* AllInputsWithMatchingOutputAreSpent
=============================================================================