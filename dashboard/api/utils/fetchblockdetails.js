import WebSocket from 'ws';
import { rpcWithEnv } from './rpcWithEnv.js';

let lastBlockHash = null;

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

    // Check for new block or first run
    const isFirstRun = lastBlockHash === null;
    const isNewBlock = blockHash !== lastBlockHash;

    if (!isFirstRun && !isNewBlock) {
      return;
    }

    console.log(`Fetching block: ${blockHash} at height ${latestHeight}`);
    lastBlockHash = blockHash;

    const blockData = await rpcWithEnv({
      method: 'getblock',
      params: [blockHash, 2],
    });

    const coinbaseTx = blockData.tx[0];
    const rewardBTC = coinbaseTx.vout.reduce((acc, out) => acc + out.value, 0);

    const transactions = blockData.tx.slice(1).map((tx, index) => {
      const feeBTC = typeof tx.fee === 'number' ? Math.abs(tx.fee) : 0;
      const size = tx.size || tx.vsize || (tx.weight ? tx.weight / 4 : 225);
      const feeRate = size > 0 ? (feeBTC * 1e8) / size : 0;

      return {
        id: `${blockHash}_tx_${index}`,
        hash: tx.txid,
        timestamp: blockData.time * 1000,
        count: index + 1,
        blockId: latestHeight.toString(),
        fee: feeBTC,
        size,
        feeRate: Math.round(feeRate),
        inputs: tx.vin.length,
        outputs: tx.vout.length,
      };
    });

    const blockPayload = {
      type: 'block_data',
      data: {
        blockHash: blockData.hash,
        timestamp: blockData.time * 1000,
        height: latestHeight,
        difficulty: blockData.difficulty,
        txCount: blockData.tx.length,
        nonCoinbaseTxCount: transactions.length,
        reward: rewardBTC,
        parent: blockData.previousblockhash,
        transactions,
      },
    };

    const validTransactions = transactions.filter((tx) => tx.fee > 0);
    const totalFees = validTransactions.reduce((acc, tx) => acc + tx.fee, 0);
    const avgFeeRate =
      validTransactions.length > 0
        ? validTransactions.reduce((acc, tx) => acc + tx.feeRate, 0) /
          validTransactions.length
        : 0;
    const avgTxSize =
      validTransactions.length > 0
        ? validTransactions.reduce((acc, tx) => acc + tx.size, 0) /
          validTransactions.length
        : 0;

    let mempoolSize = 0;
    try {
      const mempoolInfo = await rpcWithEnv({ method: 'getmempoolinfo' });
      mempoolSize = mempoolInfo.size;
    } catch (err) {
      console.warn('Failed to get mempool info:', err.message);
      mempoolSize = -1;
    }

    const statsPayload = {
      type: 'transaction_stats',
      data: {
        mempoolSize,
        avgFeeRate: Math.round(avgFeeRate),
        avgTxSize: Math.round(avgTxSize),
        txRate: transactions.length,
        totalFees,
        blockTransactionCount: transactions.length,
      },
    };

    // Store latest payloads
    latestBlockPayload = blockPayload;
    latestStatsPayload = statsPayload;

    console.log('Block fetching details : ', blockPayload.data);
    console.log('Mempool fetching details : ', statsPayload.data);

    const blockMessage = JSON.stringify(blockPayload);
    const statsMessage = JSON.stringify(statsPayload);

    let sentCount = 0;
    wss.clients.forEach((client) => {
      if (client.readyState === WebSocket.OPEN) {
        try {
          client.send(blockMessage);
          client.send(statsMessage);
          sentCount++;
        } catch (err) {
          console.error('Failed to send to client:', err.message);
        }
      }
    });
  } catch (err) {
    console.error('Block fetch failed:', err.message);

    const errorPayload = {
      type: 'error',
      data: {
        message: `Failed to fetch block data: ${err.message}`,
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
}
