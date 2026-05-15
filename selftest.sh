#!/bin/sh

# This self test expects bitcoin to be running on the same host, and configured
# to expose its ZMQ interface on port 28332.

cd node
cargo build
cargo run -- --bind=127.0.0.1:8000 --stratum-port=3333 --rpc-bind=127.0.0.1:6682 &
sleep 1
cargo run -- --addnode=/ip4/127.0.0.1/udp/8000/quic-v1 --bind=127.0.0.1:9000 --stratum-port=3334 --rpc-bind=127.0.0.1:6683 &
sleep 1
echo
echo ">>> Press Enter to exit"
read -r _

killall node
