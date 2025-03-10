#!/bin/sh

cd node
cargo build
cargo run -- --bind=localhost:25188 --network=cpunet --rpccookie=~/.bitcoin/cpunet/.cookie --rpcport=28332 &
sleep 1
cargo run -- --bind=localhost:25189 --network=cpunet --rpccookie=~/.bitcoin/cpunet/.cookie --rpcport=28332 --addnode=localhost:25188 &
sleep 1

echo
echo ">>> Press any key to exit"
read

killall braidpool-node
