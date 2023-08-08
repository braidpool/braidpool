-------------------------------- MODULE UHPO --------------------------------
(*
In this spec we describe the maintenance of UHPO and the coinbase inputs that
it spends.

Assume the following protocols are specified elsewhere:

1. pool key maintenance, i.e. DKG
2. threshold signatures, i.e. TSS
3. Pool participants maintenance

We specify the following operatos:

1. AddMiner - 
2. RemoveMiner
3. PayMiner - a miner is paid while continuing in the pool
4. UpdatePayouts - new shares with varying difficulty are to be rewarded. 
                Here we need to compute the weighted average and 
                distribute the reward. 
                
The actions when UHPO is update is are:

1. FindBitcoinBlock - pool finds a new block, we need to create new coinbase
                      and construct an updated uhpo transaction that spends
                      old coinbases and updates the payout amounts for miners
    
2. NewBlockReceived - a new bitcoin block is found, we use this as the
                      clock for scheduled updates to rotate pool key
                      (add/remove/payout miners) and to generate a new 
                      pool key - i.e. run DKG as well as TSS to sign new
                      UHPO output
*)

-----------------------------------------------------------------------------

\* AddMiner == 

=============================================================================