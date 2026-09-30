import WebSocket from 'ws';
import { rpcWithEnv } from './rpcWithEnv.js';

let lastBlockHash = null;
let blockHistory = [];
const AVERAGING_WINDOW = 10;

export let latestBlockPayload = null;
export let latestStatsPayload = null;

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

    const coinbaseTx = blockData.tx[0];

    const reward = coinbaseTx.vout.reduce((acc, vout) => acc + vout.value, 0);

    console.log(`Reward: ${reward} BTC`);
    console.log(`Number of transactions in this block: ${blockData.tx.length}`);

    const blockInfo = {
      height: latestHeight,
      timestamp: blockData.time,
      txCount: blockData.tx.length - 1,
      hash: blockData.hash,
    };

    blockHistory.push(blockInfo);
    if (blockHistory.length > AVERAGING_WINDOW) {
      blockHistory.shift();
    }

    const txRates = calculateTransactionRates(blockHistory);

    let mempoolSize = 0;
    try {
      const mempoolInfo = await rpcWithEnv({ method: 'getmempoolinfo' });
      mempoolSize = mempoolInfo.size;
    } catch (err) {
      console.warn('Failed to get mempool info:', err.message);
      mempoolSize = -1;
    }

    const { difficulty, tx, previousblockhash, hash, time } = blockData;
    const blockPayload = {
      type: 'block_data',
      data: {
        blockHash: hash,
        timestamp: time * 1000,
        height: latestHeight,
        difficulty,
        txCount: tx.length,
        nonCoinbaseTxCount: tx.length - 1,
        reward,
        parent: previousblockhash,
      },
    };

    const statsPayload = {
      type: 'transaction_stats',
      data: {
        mempoolSize,
        avgFeeRate: 0,
        avgTxSize: 0,
        txRate: txRates.movingAverage,
        averagingWindow: blockHistory.length,
      },
    };

    console.log(
      `Moving Avg (${blockHistory.length} blocks): ${txRates.movingAverage} tx/min`
    );
    console.log(`Time Between Last 2 Blocks: ${txRates.lastBlockTime}s`);

    latestBlockPayload = blockPayload;
    latestStatsPayload = statsPayload;

    broadcastToClients(wss, blockPayload, statsPayload);
  } catch (err) {
    console.error('Block fetch failed:', err.message);
    broadcastError(wss, err);
  }
}

function calculateTransactionRates(blockHistory) {
  if (blockHistory.length < 2) {
    return {
      movingAverage: 0,
      lastBlockTime: 0,
    };
  }

  const latest = blockHistory[blockHistory.length - 1];
  const previous = blockHistory[blockHistory.length - 2];
  const lastBlockTime = Math.max(latest.timestamp - previous.timestamp, 1);

  // Calculate moving average over available window
  const first = blockHistory[0];
  const totalTime = latest.timestamp - first.timestamp; // seconds
  const totalTxs = blockHistory.reduce((sum, block) => sum + block.txCount, 0);

  // Convert to tx/min (if totalTime > 0)
  const movingAverage =
    totalTime > 0 ? Math.round((totalTxs / (totalTime / 60)) * 100) / 100 : 0;

  return {
    movingAverage,
    lastBlockTime,
  };
}

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
