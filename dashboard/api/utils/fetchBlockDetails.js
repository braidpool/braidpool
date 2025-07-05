import WebSocket from 'ws';
import { rpcWithEnv } from './rpcWithEnv.js';

let lastBlockHash = null;

export let latestBlockPayload = null;
export let latestStatsPayload = null;

// Minimum time between blocks (seconds) to prevent unrealistic tx rate spikes
const MIN_BLOCK_TIME_SEC = 10;

export async function fetchBlockDetails(wss) {
  try {
    const blockchainInfo = await rpcWithEnv({ method: 'getblockchaininfo' });
    const latestHeight = blockchainInfo.blocks;

    const blockHash = await rpcWithEnv({
      method: 'getblockhash',
      params: [latestHeight],
    });

    // Skip if no new block
    if (blockHash === lastBlockHash && lastBlockHash !== null) {
      return;
    }

    console.log(`Fetching block: ${blockHash} at height ${latestHeight}`);
    lastBlockHash = blockHash;

    const blockData = await rpcWithEnv({
      method: 'getblock',
      params: [blockHash, 2],
    });

    // --- Process block transactions ---
    const coinbaseTx = blockData.tx[0];
    const rewardBTC = coinbaseTx.vout.reduce((acc, out) => acc + out.value, 0);

    const transactions = blockData.tx.slice(1).map((tx, index) => ({
      id: `${blockHash}_tx_${index}`,
      hash: tx.txid,
      timestamp: blockData.time * 1000,
      count: index + 1,
      blockId: latestHeight.toString(),
      fee: typeof tx.fee === 'number' ? Math.abs(tx.fee) : 0,
      size: tx.size || tx.vsize || (tx.weight ? tx.weight / 4 : 225),
      feeRate: Math.round((tx.fee * 1e8) / (tx.size || tx.vsize || 225)),
      inputs: tx.vin.length,
      outputs: tx.vout.length,
    }));

    // --- Calculate tx rate (transactions per minute) ---
    const previousBlockData = await rpcWithEnv({
      method: 'getblock',
      params: [blockData.previousblockhash, 1],
    });

    const timeDiffSeconds = Math.max(
      blockData.time - previousBlockData.time,
      MIN_BLOCK_TIME_SEC
    );
    const nonCoinbaseTxCount = blockData.tx.length - 1;
    const txRatePerMin = (nonCoinbaseTxCount / timeDiffSeconds) * 60;

    // --- Mempool stats ---
    let mempoolSize = 0;
    try {
      const mempoolInfo = await rpcWithEnv({ method: 'getmempoolinfo' });
      mempoolSize = mempoolInfo.size;
    } catch (err) {
      console.warn('Failed to get mempool info:', err.message);
      mempoolSize = -1;
    }

    // --- Fee/size stats ---
    const validTransactions = transactions.filter((tx) => tx.fee > 0);
    const totalFees = validTransactions.reduce((acc, tx) => acc + tx.fee, 0);
    const avgFeeRate =
      validTransactions.length > 0
        ? Math.round(
            validTransactions.reduce((acc, tx) => acc + tx.feeRate, 0) /
              validTransactions.length
          )
        : 0;
    const avgTxSize =
      validTransactions.length > 0
        ? Math.round(
            validTransactions.reduce((acc, tx) => acc + tx.size, 0) /
              validTransactions.length
          )
        : 0;

    // --- Build payloads ---
    const blockPayload = {
      type: 'block_data',
      data: {
        blockHash: blockData.hash,
        timestamp: blockData.time * 1000,
        height: latestHeight,
        difficulty: blockData.difficulty,
        txCount: blockData.tx.length,
        nonCoinbaseTxCount,
        reward: rewardBTC,
        parent: blockData.previousblockhash,
        transactions,
      },
    };

    const statsPayload = {
      type: 'transaction_stats',
      data: {
        mempoolSize,
        avgFeeRate,
        avgTxSize,
        txRate: Math.round(txRatePerMin),
        totalFees,
        blockTransactionCount: transactions.length,
      },
    };

    // Update and broadcast
    latestBlockPayload = blockPayload;
    latestStatsPayload = statsPayload;

    broadcastToClients(wss, blockPayload, statsPayload);
  } catch (err) {
    console.error('Block fetch failed:', err.message);
    broadcastError(wss, err);
  }
}

// Helper: Broadcast data to all connected clients
function broadcastToClients(wss, blockPayload, statsPayload) {
  const blockMsg = JSON.stringify(blockPayload);
  const statsMsg = JSON.stringify(statsPayload);

  wss.clients.forEach((client) => {
    if (client.readyState === WebSocket.OPEN) {
      try {
        client.send(blockMsg);
        client.send(statsMsg);
      } catch (err) {
        console.error('Failed to send to client:', err.message);
      }
    }
  });
}

// Helper: Broadcast errors
function broadcastError(wss, err) {
  const errorPayload = {
    type: 'error',
    data: {
      message: `Block data fetch failed: ${err.message}`,
      timestamp: Date.now(),
      error: err.code || 'UNKNOWN_ERROR',
    },
  };

  wss.clients.forEach((client) => {
    if (client.readyState === WebSocket.OPEN) {
      try {
        client.send(JSON.stringify(errorPayload));
      } catch (sendErr) {
        console.error('Failed to send error to client:', sendErr.message);
      }
    }
  });
}
