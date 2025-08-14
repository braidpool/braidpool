# IPC Braidpool

Braidpool uses Inter-Process Communication (IPC) to connect with Bitcoin Core using UNIX domain sockets for efficient, low-latency communication compared to traditional ZMQ or RPC methods.

## Prerequisites

- Bitcoin Core with IPC support enabled
- Unix-domain socket support (Linux/macOS)
- Cap'n Proto development libraries
- libmultiprocess library

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
  ./bitcoin-node -ipcbind=unix:/tmp/bitcoin-ipc.sock -printtoconsole
  ```
  
  here `/tmp` is the path and `bitcoin-ipc.sock` is the name of the Unix socket and you can change this according to your usage.
  
## Build and Run Braidpool
A Braidpool node can be built using different configurations related to IPC. Check `braidpool/node/src/cli.rs` to find all available CLI options.

#### Start Braidpool with IPC:
```sh
cd braidpool/node

# With minimal options
cargo run -- \
  --ipc \
  --ipc-socket /tmp/bitcoin-ipc.sock \
  --network mainnet

# With additional options
cargo run -- \
  --ipc \
  --ipc-socket /tmp/bitcoin-ipc.sock \
  --network regtest \
  --bind 127.0.0.1:6680 \
  --datadir ~/.braidpool/
```
#### CLI Options:

You can find all available command-line arguments in [node/src/cli.rs](https://github.com/braidpool/braidpool/blob/main/node/src/cli.rs).

-   `--ipc`: Enables IPC communication mode.
-   `--ipc-socket <PATH>`: Specifies the path to the UNIX domain socket file (should be the same as bitcoin node).
-   `--network <NETWORK>`: Sets the network. Valid options are `mainnet`, `testnet4`, `signet`, and `cpunet`. The default is `mainnet`.