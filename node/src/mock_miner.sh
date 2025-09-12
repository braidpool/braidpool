#!/bin/bash

set -e  

sudo apt update
sudo apt install -y git automake autoconf build-essential libcurl4-openssl-dev

git clone https://github.com/pooler/cpuminer.git
cd cpuminer

./autogen.sh
./nomacro.pl
./configure CFLAGS="-O3"
make

