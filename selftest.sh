#!/bin/sh

cd node
cargo build
cargo run -- --bitcoin=0.0.0.0 --rpcport=8332 --rpcuser=xxxx --rpcpass=yyyy --zmqhashblockport=28332 --multiaddr=/ip4/127.0.0.1/udp/8000/quic-v1 &
sleep 1
cargo run -- --addnode=/ip4/127.0.0.1/udp/8000/quic-v1 --bitcoin=0.0.0.0 --rpcport=8332 --rpcuser=xxxx --rpcpass=yyyy --zmqhashblockport=28332 --multiaddr=/ip4/127.0.0.1/udp/9000/quic-v1 &
sleep 1

echo
echo ">>> Press any key to exit"
read

killall node
