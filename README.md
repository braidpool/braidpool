![Build status](https://github.com/wholooks/braidpool/actions/workflows/rust-node.yml/badge.svg)

# Proposal

Read the
[Overview](https://github.com/braidpool/braidpool/blob/master/docs/overview.md)
for [General Considerations for Decentralized Mining Pools](https://github.com/braidpool/braidpool/blob/master/docs/general_considerations.md), or [Braidpool Spec](https://github.com/braidpool/braidpool/blob/master/docs/braidpool_spec.md) in increasing levels of complexity. You may also be interested in our [Roadmap](https://github.com/braidpool/braidpool/blob/master/docs/roadmap.md)

The goals of the pool are:

1. Lower variance for independent miners, even when large miners join the pool.
2. Miners build their own blocks, just like in p2pool.
3. Payouts require a constant size blockspace, independent of the number of
   miners on the pool.
4. Provide building blocks for enabling a futures market of hash rates.

# Running the node

Braidpool nodes need to connect to a bitcoin RPC node. The bitcoin node also needs to have the `hashblock` [ZMQ notification](https://github.com/bitcoin/bitcoin/blob/master/doc/zmq.md) enabled.

Let's assume there is a `bitcoind` running on `0.0.0.0:8332` with username `xxxx`, password `yyyy`, and `zmqpubhashblock` enabled on port `28332`:

```
$ bitcoind -rpcport=8332 -rpcuser=xxxx -rpcpassword=yyyy -zmqpubhashblock=tcp://localhost:28332
```

For the moment, the braidpool node runs a simple p2p broadcast. To run it you need to do
the usual cargo things

```
cd node
cargo build

# run the first seed node on port 8989
cargo run -- --bind=localhost:8989 --bitcoin=0.0.0.0 --rpcport=8332 --rpcuser=xxxx --rpcpass=yyyy --zmqhashblockport=28332

# run other nodes pointing to the seeding node and specify their own port as 9899
cargo run -- --bind=localhost:9899 --addnode=localhost:8989 --bitcoin=0.0.0.0 --rpcport=8332 --rpcuser=xxxx --rpcpass=yyyy --zmqhashblockport=28332
```

# Running the CPUnet testing node using nix-script

Setting up `nix` locally for utilizing it from the specific releases check - [Nix setup](https://github.com/DeterminateSystems/nix-installer/releases)

```
curl --proto '=https' --tlsv1.2 -sSf -L https://install.determinate.systems/nix | \
  sh -s -- install
```

The `.nix` script present in the root directory `/braidpool/cpunet_node.nix` contains the CPUnet patched
bitcoin-node , can be set up locally as testnet for Braidpool.

```
# Path to the parent directory
cd /braidpool

# Run the nix-script
nix-build cpunet_node.nix

# Path to the result directory created after successful build
cd result

# Running the CPUnet node
./bin/bitcoind -cpunet -zmqpubsequence=tcp://127.0.0.1:28338

# Creating/loading a corresponding wallet
./bin/bitcoin-cli -cpunet createwallet cpunet

# Load an  wallet created previously
./bin/bitcoin-cli -cpunet loadwallet cpunet

# Generate blocks
./contrib/cpunet/miner --cli=./bin/bitcoin-cli --ongoing --address `./bin/bitcoin-cli -cpunet getnewaddress` --grind-cmd="./bin/bitcoin-util -cpunet -ntasks=1 grind"


```

# Documentation

The documentation is in the `docs/` directory and contains a bunch of math. To
view it locally rendered in your browser including the math, use
[MkDocs](https://www.mkdocs.org/):

```
cd braidpool
mkdocs serve
xdg-open http://localhost:8000
```

Or you can just click on the docs directory in the code and Github will render the math in these markdown docs.

# Braidpool Dashboard

A visualization dashboard for the Braidpool decentralized mining pool, and Bitcoin related data.
###  Quick Setup

For setup instructions and environment configuration, please refer to the  
➡️ [Dashboard README](./dashboard/README.md)


# Progress

A list with TODO's:

- [x] Global simulator for Braids (`tests/simulator.py`)
- [x] Python braid `cohorts()` implementation and tests
- [x] Rust braid object handling
- [ ] Connect braid algorithms to blocks on CPUNet
- [ ] P2P gossip based broadcast of miner blocks and shares.
- [ ] Use FROST rust implementation for providing threshold schnorr
      signatures. Use mock clock for identifying rounds.
- [ ] Validate received blocks and shares.
- [ ] Single script installer (limited to Linux variants, potentially using
      docker).

[Discord chat](https://discord.gg/pZYUDwkpPv)
