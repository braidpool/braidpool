# IPC Braidpool

Braidpool uses Inter-Process Communication (IPC) to connect with Bitcoin Core using UNIX domain sockets for efficient, low-latency communication compared to traditional ZMQ or RPC methods.

## Prerequisites

- Bitcoin Core with IPC support enabled.
- Unix-domain socket support (Linux/macOS).
- Cap'n Proto development libraries.
- libmultiprocess library.
- cpuminer for downstream connection (if no external ASIC).

## Building Bitcoin
First to connect with Braidpool you need to build your Bitcoin node with IPC enabled build configurations. Check out bitcoin [multiprocess](https://github.com/bitcoin/bitcoin/blob/master/doc/multiprocess.md) doc to get the information about building with IPC.

For a quick reference these are the steps you can follow:
- Install and configure [libmultiprocess](https://github.com/bitcoin-core/libmultiprocess) and [Cap'n Proto](https://capnproto.org/) as dependencies to your system.
- Build bitcoin node as:
  ```
  cd <BITCOIN_SOURCE_DIRECTORY>
  cmake -B build -DENABLE_IPC=ON
  cmake --build build
  ```
- This will create a `build` folder and inside this there is a `bin` folder. In this you will find all the executables, including `bitcoin-node`, `bitcoind`, `bitcoin-cli` etc.
  
Note: The above steps will only work if you have already installed `libmultiprocess` and `Cap'n Proto` dependencies locally on your system.

## Run Bitcoin with IPC
To run the bitcoin-node process with an explicit UNIX socket name and location:

  ```
  cd build/bin
  ./bitcoin-node -cpunet -ipcbind=unix:/tmp/bitcoin-cpunet.sock -printtoconsole
  ```
  
  here `/tmp` is the path and `bitcoin-cpunet.sock` is the name of the Unix socket and you can change this according to your usage.
  
## Build and Run Braidpool
A Braidpool node can be built using different configurations related to IPC. Check `braidpool/node/src/cli.rs` to find all available CLI options.

Before running `braidpool/node` make sure you have rust-toolchain and rustc installed along with cargo as the package-manager .

```
# Refer here for setting up rust development environment 
https://rust-lang.org/tools/install/
```

#### Start Braidpool with IPC:
```sh
cd braidpool/node

# With minimal options
cargo run -- \
  --network cpunet

# With additional options
cargo run -- \
  --ipc-socket /tmp/bitcoin-cpunet.sock \
  --network cpunet \
  --bind 127.0.0.1:6680 \
  --datadir ~/.braidpool/
```
#### CLI Options:

You can find all available command-line arguments in [node/src/cli.rs](https://github.com/braidpool/braidpool/blob/main/node/src/cli.rs).

-   `--ipc-socket <PATH>`: Specifies the path to the UNIX domain socket file (should be the same as bitcoin node).
-   `--network <NETWORK>`: Sets the network. Valid options are `mainnet`, `testnet4`, `signet`, and `cpunet`. The default is `mainnet`.

## For probing current braidpool-node 
- `braidpool-cli` crate can be utilized for accessing current braid-state including information about the `bead-count`,`bead-by-beadhash`,`tips` etc.
```
  # Change to cli-directory after running `node`
  cd braidpool-cli 
  
  # Running the cli commands for current braid-state
  cargo run -- gettips

  # Run --help for getting information about existing commands
  cargo run -- --help

```
## Setting up cpuminer for downstream connection
  - If you don't have a physical miner, you can use CPUMiner to run tests on Bitcoin `mainnet`, `testnet4`, or `signet`. CPUMiner does not support the `cpunet` network, because CPUNet uses a different block-header hash algorithm; to mine on CPUNet with a CPU, use our CPUNet-specific `rust_cpunet_miner` as described below.
  - For mining over cpunet on CPU you can run our cpunet configured rust_cpu_miner instructions here - `https://github.com/braidpool/rust_cpunet_miner` .
  - For mining over other testnets,firstly install `cpuminer` for connecting a downstream to the node's stratum service (can be done by any external ASIC device or cpu based).

  - Run the `node/src/mock_miner.sh` script for the installation in the cwd for cpuminerd setup.

  - Execute the `minerd` process via console/terminal by 
    `./minerd -a sha256d -o stratum+tcp://localhost:3333 -q -D -P`.

  - Password and downstream device name are optional paramateres can be sent if required for more information  check the source repository 
  `https://github.com/pooler/cpuminer` .

  - Run the `braidpool-binary` as stated above via `cargo run` for the logs to be seen in the console.
