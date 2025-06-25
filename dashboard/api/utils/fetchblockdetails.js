import WebSocket from 'ws';
import { rpcWithEnv } from './rpcWithEnv.js';

let lastBlockHash = null;

export async function fetchBlockDetails(wss) {
  try {
    const startTime = Date.now();
    const blockchainInfo = await rpcWithEnv({ method: 'getblockchaininfo' });
    const latestHeight = blockchainInfo.blocks;

    const blockHash = await rpcWithEnv({
      method: 'getblockhash',
      params: [latestHeight],
    });

    if (blockHash === lastBlockHash) {
      console.log(` No new block at height ${latestHeight}`);
      return;
    }

    lastBlockHash = blockHash;

    const blockData = await rpcWithEnv({
      method: 'getblock',
      params: [blockHash, 2],
    });

    const coinbaseTx = blockData.tx[0];
    const rewardBTC = coinbaseTx.vout.reduce((acc, out) => acc + out.value, 0);

    const transactions = blockData.tx.slice(1).map((tx, index) => {
      const feeBTC = tx.fee !== undefined ? tx.fee : 0.0001;
      const size = tx.size || tx.weight || 225;
      const feeRate = size > 0 ? (feeBTC * 1e8) / size : 0;

      return {
        id: `${blockHash}_tx_${index}`,
        hash: tx.txid,
        timestamp: blockData.time * 1000,
        count: index + 1,
        blockId: latestHeight.toString(),
        fee: feeBTC,
        size: size,
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
        reward: rewardBTC,
        parent: blockData.previousblockhash,
        transactions,
      },
    };

    const totalFees = transactions.reduce((acc, tx) => acc + tx.fee, 0);
    const avgFeeRate =
      transactions.length > 0
        ? transactions.reduce((acc, tx) => acc + tx.feeRate, 0) /
          transactions.length
        : 0;
    const avgTxSize =
      transactions.length > 0
        ? transactions.reduce((acc, tx) => acc + tx.size, 0) /
          transactions.length
        : 0;

    const statsPayload = {
      type: 'transaction_stats',
      data: {
        mempoolSize: blockData.tx.length - 1,
        avgFeeRate: avgFeeRate,
        avgTxSize: Math.round(avgTxSize),
        txRate: blockData.tx.length - 1,
        totalFees: totalFees,
      },
    };

    wss.clients.forEach((client) => {
      if (client.readyState === WebSocket.OPEN) {
        client.send(JSON.stringify(blockPayload));
        client.send(JSON.stringify(statsPayload));
      }
    });

    console.log(`Block ${latestHeight} sent in ${Date.now() - startTime}ms`);
  } catch (err) {
    console.error(' Block fetch failed:', err.message);
  }
}
