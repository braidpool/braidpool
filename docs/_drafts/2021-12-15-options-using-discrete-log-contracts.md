---
layout: post
title: "Providing Options Contracts Using Discrete Log Contracts"
image: assets/BC_Logo_.png
---

Braidpool provides facilities that will be useful to write futures and
options contracts. This post defines our understanding what these
contracts look like and which assets are involved in the contracts. We
also provide a high level design of how these can be provided with the
building blocks presented in the
[proposal](https://github.com/pool2win/braidpool/raw/main/proposal/proposal.pdf).

# Futures and Options Contracts

Both futures and options are derivates that can be used to hedge
risk. The raison d'etre for these derivates is to allow the producer
of a commodity to manage their risk of being unable to produce enough
of the commodity.

In the case of bitcoin, the commodity that miners produce are Exa
Hashes. The price of this commodity in terms of BTC fluctuates
according to conditions outside the control of the miner and that is
what the miners want to hedge.

In a situation like this, the producer of the commodity can buy a call
option, such that if the price of the commodity falls, they can buy
the commodity at an agreed upon price and sell it immediately to earn
a profit.

In our case, say a miner starts mining and aims to produce 1000 EH
over a six month period hoping to earn 10 BTC. The risk the miner
faces is that over the six month period the difficulty goes up and
they only produce 5 BTC. To hedge against this, the miner can buy an
put option that gives the miner an option to buy BTC at 


## Futures

## Call Option

## Put Option


# DAG of Shares, Seals and DLC

[Discrete Log Contracts](https://dci.mit.edu/smart-contracts)(DCL) can
be used to provide an options contract between two parties such that
no details are revealed to the blockchain. The DCL construction is
similar to a [Scriptless
Scripts](https://github.com/ElementsProject/scriptless-scripts) in
terms of how they use Schnorr Signature to avoid the blockchain
knowing anything more than it needs to know.

One of the stated goals of braidpool is to provide 
