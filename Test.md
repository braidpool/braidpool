# Testing Guide

## Prerequisites

- Bitcoin Core (with regtest nodes already running and synced)
- Rust toolchain
- jq (for JSON formatting)

## Configuration

### 1. Configure Nodes

Create configuration files for both nodes:

```bash
# bitcoind_node/bitcoin.conf
regtest=1
server=1
txindex=1
rpcuser=YOUR_USERNAME
rpcpassword=YOUR_PASSWORD
rpcport=18332
rpcbind=127.0.0.1
rpcallowip=127.0.0.1

# cmempoold_node/bitcoin.conf
regtest=1
server=1
txindex=1
rpcuser=YOUR_USERNAME
rpcpassword=YOUR_PASSWORD
rpcport=19443
rpcbind=127.0.0.1
rpcallowip=127.0.0.1
```

### 2. Configure Environment

Create `.env` file in `braidpoold/` directory:

```bash
BITCOIND_URL=http://127.0.0.1:18332
BITCOIND_USER=YOUR_USERNAME
BITCOIND_PASS=YOUR_PASSWORD

CMEMPOOL_URL=http://127.0.0.1:19443
CMEMPOOL_USER=YOUR_USERNAME
CMEMPOOL_PASS=YOUR_PASSWORD

API_HOST=127.0.0.1
API_PORT=3001
```

## Running the API Server

```bash
cd braidpoold
cargo run
```

Expected output:

```
Standard node block count: 101
Committed node block count: 101
API running at http://127.0.0.1:3001
```

## Testing Transaction Categories

Set your environment variables:

```bash
export RPC_USER="YOUR_USERNAME"
export RPC_PASS="YOUR_PASSWORD"
export WALLET_NAME="your_wallet"
export ADDRESS="bcrt1qa2sr0ehdyp48a5t74uxaexpd90em43vqxt4djy"
```

### Helper Function

```bash
create_tx() {
    TXID=$(bitcoin-cli -regtest -rpcuser=$RPC_USER -rpcpassword=$RPC_PASS -rpcport=18332 \
      -rpcwallet=$WALLET_NAME sendtoaddress "$ADDRESS" 0.001)

    RAW=$(bitcoin-cli -regtest -rpcuser=$RPC_USER -rpcpassword=$RPC_PASS -rpcport=18332 \
      -rpcwallet=$WALLET_NAME gettransaction "$TXID" | jq -r '.hex')

    bitcoin-cli -regtest -rpcuser=$RPC_USER -rpcpassword=$RPC_PASS -rpcport=18332 \
      sendrawtransaction "$RAW" > /dev/null

    echo $TXID
}
```

### Test 1: Mempool

```bash
TX1=$(create_tx)
sleep 1
curl -s http://localhost:3001/tx/$TX1 | jq '{txid, category, fee_rate}'
# Expected: category = "Mempool"
```

### Test 2: Committed

```bash
TX2=$(create_tx)
sleep 1
curl -s -X POST http://localhost:3001/transactions/$TX2/commit | jq
sleep 1
curl -s http://localhost:3001/tx/$TX2 | jq '{txid, category, fee_rate}'
# Expected: category = "Committed"
```

### Test 3: Proposed

```bash
TX3=$(create_tx)
sleep 1
curl -s -X POST http://localhost:3001/transactions/$TX3/commit | jq
curl -s -X POST http://localhost:3001/transactions/$TX3/propose | jq
sleep 1
curl -s http://localhost:3001/tx/$TX3 | jq '{txid, category, fee_rate}'
# Expected: category = "Proposed"
```

### Test 4: Scheduled

```bash
TX4=$(create_tx)
sleep 1
curl -s -X POST http://localhost:3001/transactions/$TX4/commit | jq
curl -s -X POST http://localhost:3001/transactions/$TX4/propose | jq
curl -s -X POST http://localhost:3001/transactions/$TX4/schedule | jq
sleep 1
curl -s http://localhost:3001/tx/$TX4 | jq '{txid, category, fee_rate}'
# Expected: category = "Scheduled"
```

### Test 5: Confirmed

```bash
TX5=$(create_tx)
sleep 1

# Mine a block
bitcoin-cli -regtest -rpcuser=$RPC_USER -rpcpassword=$RPC_PASS -rpcport=18332 -generate 1 > /dev/null

# Sync block to cmempool
HEIGHT=$(bitcoin-cli -regtest -rpcuser=$RPC_USER -rpcpassword=$RPC_PASS -rpcport=18332 getblockcount)
HASH=$(bitcoin-cli -regtest -rpcuser=$RPC_USER -rpcpassword=$RPC_PASS -rpcport=18332 getblockhash $HEIGHT)
HEX=$(bitcoin-cli -regtest -rpcuser=$RPC_USER -rpcpassword=$RPC_PASS -rpcport=18332 getblock $HASH 0)
bitcoin-cli -regtest -rpcuser=$RPC_USER -rpcpassword=$RPC_PASS -rpcport=19443 submitblock "$HEX" > /dev/null

sleep 2
curl -s http://localhost:3001/tx/$TX5 | jq '{txid, category, confirmations}'
# Expected: category = "Confirmed", confirmations = 1
```

## View All Transactions

```bash
# Get all transactions grouped by category
curl -s http://localhost:3001/transactions | \
  jq 'group_by(.category) | map({category: .[0].category, count: length})'

# Get transaction details
curl -s http://localhost:3001/transactions | \
  jq '.[] | {txid, category, fee_rate, size}'
```

## API Endpoints

- `GET /transactions` - List all transactions
- `GET /tx/{txid}` - Get transaction details
- `GET /mempool/info` - Get mempool statistics
- `POST /transactions/{txid}/commit` - Move transaction to Committed
- `POST /transactions/{txid}/propose` - Move transaction to Proposed
- `POST /transactions/{txid}/schedule` - Move transaction to Scheduled

## Troubleshooting

**API connection failed:**

```bash
# Verify .env file is configured correctly
cat braidpoold/.env

# Check API output shows correct block counts
cargo run
```

**Transaction not found:**

```bash
# Ensure transaction was broadcast
bitcoin-cli -regtest -rpcuser=$RPC_USER -rpcpassword=$RPC_PASS -rpcport=18332 getrawmempool
```
