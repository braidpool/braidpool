**Prerequisites**
[x] Bitcoin Core
[x] Rust toolchain
[x] jq (for JSON formatting)

**Setup**
**start both nodes**
[x] Bitcoind Node (Standard):

```bash
# Terminal 1
cd bitcoind_node
./start.sh

```

[x] Cmempool Node (Committed Mempool):

```bash
# Terminal 2
cd cmempoold_node
./start.sh

```

**Verify both nodes are running:**
Replace `<RPCUSER>`, `<RPC_PASSWORD>`, `<CMEMPOOL_USER>`, `<CMEMPOOL_PASSWORD>` with values from your `bitcoin.conf` files.

```bash
# Bitcoind
bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 getblockcount

# Cmempool
bitcoin-cli -regtest -rpcuser=<CMEMPOOL_USERNAME> -rpcpassword=<CMEMPOOL_PASSWORD> -rpcport=19443 getblockcount

# both should be same or 0 - fresh start
```

**Ensure Nodes Are Synced**

```bash
# Both nodes must have the same blockchain state.

STD_HASH=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 getbestblockhash)
CM_HASH=$(bitcoin-cli -regtest -rpcuser=<CMEMPOOL_USERNAME> -rpcpassword=<CMEMPOOL_PASSWORD> -rpcport=19443 getbestblockhash)

echo "Bitcoind:  $STD_HASH"
echo "Cmempool:  $CM_HASH"

if [ "$STD_HASH" == "$CM_HASH" ]; then
    echo "SYNCED"
else
    echo "Not SYNCED"
```

**Create Wallet and Generate Spendable Coins**

[x] Create wallet

```bash
# Create wallet
bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 createwallet "WALLET_NAME"
#  You may need to load the wallet manually

# or
bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  createwallet "WALLET_NAME" false false "" false false true

# Generate blocks to fund wallet
bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -rpcwallet=<WALLET_NAME> -generate 101

# Verify wallet has funds
bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -rpcwallet=<WALLET_NAME> getbalance


```

# Sync to cmempool

```bash
for height in {1..101}; do
    HASH=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 getblockhash $height)
    HEX=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 getblock $HASH 0)
    bitcoin-cli -regtest -rpcuser=<CMEMPOOL_USER> -rpcpassword=<CMEMPOOL_PASSWORD> -rpcport=19443 submitblock "$HEX" > /dev/null 2>&1
done
```

**Verify nodes are synced (check BOTH height and hash):**

````bash
# Check block heights
STD_COUNT=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 getblockcount)
CM_COUNT=$(bitcoin-cli -regtest -rpcuser=<CMEMPOOL_USER> -rpcpassword=<CMEMPOOL_PASSWORD> -rpcport=19443 getblockcount)

echo "Bitcoind height: $STD_COUNT"
echo "Cmempool height: $CM_COUNT"

# Check block hashes
STD_HASH=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 getbestblockhash)
CM_HASH=$(bitcoin-cli -regtest -rpcuser=<CMEMPOOL_USER> -rpcpassword=<CMEMPOOL_PASSWORD> -rpcport=19443 getbestblockhash)

echo "Bitcoind hash: $STD_HASH"
echo "Cmempool hash: $CM_HASH"

**Start the Rust API Server**

```bash
# Terminal 3: API
cd braidpoold
cargo build & run
````

**Expected output:**

```
Standard node block count: 101
Committed node block count: 101   // MUST be same as Standard
API running at http://127.0.0.1:3000
```

# address = bcrt1qa2sr0ehdyp48a5t74uxaexpd90em43vqxt4djy. you can use this or create a new one

**Test:**

```bash
# First, create a transaction
TXID=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -rpcwallet=<WALLET_NAME> sendtoaddress "bcrt1qa2sr0ehdyp48a5t74uxaexpd90em43vqxt4djy" 0.001)

RAW=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -rpcwallet=<WALLET_NAME> gettransaction "$TXID" | jq -r '.hex')

bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  sendrawtransaction "$RAW"


# ensure the created transaction also appears in cmempoold_node, delete bitcoind_node/regtest/mempool.dat and cmempoold_node/regtest/mempool.dat, then restart both nodes.


# Now get it via API
curl -s http://localhost:3000/tx/$TXID | jq
```

**Expected Response:**

```json
{
  "txid": ".....",
  "category": "Mempool",
  "size": 141,
  "fee": 0.00000141,
  "fee_rate": 1.0,
  "inputs": 1,
  "outputs": 2,
  "confirmations": 0,
  "timestamp": 1728567890,
  "rbf_signaled": false
}
```

```bash
# API will run on port 3000, the dashboard should run separately (different).
cd dashboard
npm run dev

```

**Testing 5 Categories**

```bash
ADDRESS="bcrt1qa2sr0ehdyp48a5t74uxaexpd90em43vqxt4djy"

# 1. Mempool

TX1=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -rpcwallet=<WALLET_NAME> sendtoaddress "$ADDRESS" 0.001)

RAW1=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -rpcwallet=<WALLET_NAME> gettransaction "$TX1" | jq -r '.hex')

bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  sendrawtransaction "$RAW1" > /dev/null

sleep 1
CAT1=$(curl -s http://localhost:3000/tx/$TX1 | jq -r '.category')
echo "   TXID: $TX1"
echo "   Category: $CAT1"

# At the same time, check the dashboard to confirm the transaction appears there


# 2. Committed
# COMMITTED transaction
TX2=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -rpcwallet=<WALLET_NAME> sendtoaddress "$ADDRESS" 0.001)

RAW2=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -rpcwallet=<WALLET_NAME> gettransaction "$TX2" | jq -r '.hex')

bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  sendrawtransaction "$RAW2" > /dev/null

sleep 1

curl -s -X POST http://localhost:3000/transactions/$TX2/commit | jq
sleep 1
CAT2=$(curl -s http://localhost:3000/tx/$TX2 | jq -r '.category')
echo "   TXID: $TX2"
echo "   Category: $CAT2"

# 3. Proposed
# PROPOSED transaction
TX3=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -rpcwallet=<WALLET_NAME> sendtoaddress "$ADDRESS" 0.001)

RAW3=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -rpcwallet=<WALLET_NAME> gettransaction "$TX3" | jq -r '.hex')

bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  sendrawtransaction "$RAW3" > /dev/null


sleep 1
curl -s -X POST http://localhost:3000/transactions/$TX3/commit | jq
sleep 1
curl -s -X POST http://localhost:3000/transactions/$TX3/propose \
  -H "Content-Type: application/json" -d '{}' | jq
sleep 1
CAT3=$(curl -s http://localhost:3000/tx/$TX3 | jq -r '.category')
echo "   TXID: $TX3"
echo "   Category: $CAT3"

# 4. Scheduled
# SCHEDULED transaction

TX4=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -rpcwallet=<WALLET_NAME> sendtoaddress "$ADDRESS" 0.001)

RAW4=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -rpcwallet=<WALLET_NAME> gettransaction "$TX4" | jq -r '.hex')

bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  sendrawtransaction "$RAW4" > /dev/null

sleep 1
curl -s -X POST http://localhost:3000/transactions/$TX4/commit | jq
sleep 1
curl -s -X POST http://localhost:3000/transactions/$TX4/propose \
  -H "Content-Type: application/json" -d '{}' | jq
sleep 1
curl -s -X POST http://localhost:3000/transactions/$TX4/schedule | jq
sleep 1
CAT4=$(curl -s http://localhost:3000/tx/$TX4 | jq -r '.category')
echo "   TXID: $TX4"
echo "   Category: $CAT4"

# 5. Confirmed
# CONFIRMED transaction
TX5=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -rpcwallet=<WALLET_NAME> sendtoaddress "$ADDRESS" 0.001)

RAW5=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -rpcwallet=<WALLET_NAME> gettransaction "$TX5" | jq -r '.hex')

bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  sendrawtransaction "$RAW5" > /dev/null

sleep 1
bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -generate 1 > /dev/null

HEIGHT=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 getblockcount)
HASH=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 getblockhash $HEIGHT)
HEX=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 getblock $HASH 0)
bitcoin-cli -regtest -rpcuser=cmempoolrpc1 -rpcpassword=securepass4561 -rpcport=19443 \
  submitblock "$HEX" > /dev/null

sleep 2
CAT5=$(curl -s http://localhost:3000/tx/$TX5 | jq -r '.category')
CONF5=$(curl -s http://localhost:3000/tx/$TX5 | jq -r '.confirmations')
echo "   TXID: $TX5"
echo "   Category: $CAT5 (Confirmations: $CONF5)"
echo ""

# Summary
echo "1. Mempool:    $TX1"
echo "2. Committed:  $TX2"
echo "3. Proposed:   $TX3"
echo "4. Scheduled:  $TX4"
echo "5. Confirmed:  $TX5"
echo ""

# Category Counts
curl -s http://localhost:3000/transactions | \
  jq 'group_by(.category) | map({category: .[0].category, count: length})'

# Transaction Details
curl -s http://localhost:3000/transactions | \
  jq '.[] | {txid, category, fee, fee_rate, size, inputs, outputs}'

```
