# Testing Guide

## Prerequisites

- Bitcoin Core installed
- Rust toolchain installed  
- `jq` for JSON formatting
- Both nodes running with synced blockchain
- Wallet with spendable funds

---

## 1. Start Both Nodes

**Terminal 1 - Bitcoind Node:**
```bash
cd bitcoind_node
./start.sh
```

**Terminal 2 - Cmempool Node:**
```bash
cd cmempoold_node
./start.sh
```

---

## 2. Start the API Server

**Terminal 3:**
```bash
cd braidpoold
cargo run
```

**Expected output:**
```
API running at http://127.0.0.1:3001
```

---

## 3. Start the Dashboard

**Terminal 4:**
```bash
cd dashboard
npm run dev
```

---

## 4. Test all 5 Transaction Categories

Use address: `bcrt1qa2sr0ehdyp48a5t74uxaexpd90em43vqxt4djy`

### 4.1 Mempool Transaction
```bash
TXID=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -rpcwallet=testwallet sendtoaddress "bcrt1qa2sr0ehdyp48a5t74uxaexpd90em43vqxt4djy" 0.001)

curl -s http://localhost:3001/tx/$TXID | jq
# Expected: "category": "Mempool"
# Also check the dashboard to confirm the transaction appears there
```

### 4.2 Committed Transaction
```bash
TXID=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -rpcwallet=testwallet sendtoaddress "bcrt1qa2sr0ehdyp48a5t74uxaexpd90em43vqxt4djy" 0.001)

curl -s -X POST http://localhost:3001/transactions/$TXID/commit | jq
curl -s http://localhost:3001/tx/$TXID | jq
# Expected: "category": "Committed"
```

### 4.3 Proposed Transaction
```bash
TXID=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -rpcwallet=testwallet sendtoaddress "bcrt1qa2sr0ehdyp48a5t74uxaexpd90em43vqxt4djy" 0.001)

curl -s -X POST http://localhost:3001/transactions/$TXID/commit | jq
curl -s -X POST http://localhost:3001/transactions/$TXID/propose -H "Content-Type: application/json" -d '{}' | jq
curl -s http://localhost:3001/tx/$TXID | jq
# Expected: "category": "Proposed"
```

### 4.4 Scheduled Transaction
```bash
TXID=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -rpcwallet=testwallet sendtoaddress "bcrt1qa2sr0ehdyp48a5t74uxaexpd90em43vqxt4djy" 0.001)

curl -s -X POST http://localhost:3001/transactions/$TXID/commit | jq
curl -s -X POST http://localhost:3001/transactions/$TXID/propose -H "Content-Type: application/json" -d '{}' | jq
curl -s -X POST http://localhost:3001/transactions/$TXID/schedule | jq
curl -s http://localhost:3001/tx/$TXID | jq
# Expected: "category": "Scheduled"
```

### 4.5 Confirmed Transaction
```bash
TXID=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 \
  -rpcwallet=testwallet sendtoaddress "bcrt1qa2sr0ehdyp48a5t74uxaexpd90em43vqxt4djy" 0.001)

# Mine a block to confirm
bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 -generate 1

# Sync the new block to cmempool
HEIGHT=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 getblockcount)
HASH=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 getblockhash $HEIGHT)
HEX=$(bitcoin-cli -regtest -rpcuser=<RPCUSER> -rpcpassword=<RPC_PASSWORD> -rpcport=18332 getblock $HASH 0)
bitcoin-cli -regtest -rpcuser=<CMEMPOOL_USER> -rpcpassword=<CMEMPOOL_PASSWORD> -rpcport=19443 submitblock "$HEX"

curl -s http://localhost:3001/tx/$TXID | jq
# Expected: "category": "Confirmed", "confirmations": 1
```

---

## 5. Verify All Transactions via API

```bash
# List all transactions
curl -s http://localhost:3001/transactions | jq

# Get category counts
curl -s http://localhost:3001/transactions | \
  jq 'group_by(.category) | map({category: .[0].category, count: length})'
```

---

## Expected API Response Format

```json
{
  "txid": "...",
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
