import WebSocket from 'ws';
import { rpcWithEnv } from './rpcWithEnv.js';

export async function fetchBlockDetails(wss, blockHeight = null) {
  try {
    const startTime = Date.now();
    let height = blockHeight;
    if (!height) {
      const blockchainInfo = await rpcWithEnv({ method: 'getblockchaininfo' });
      height = blockchainInfo.blocks;
    }

    const blockHash = await rpcWithEnv({
      method: 'getblockhash',
      params: [height],
    });

    const blockData = await rpcWithEnv({
      method: 'getblock',
      params: [blockHash, 2],
    });

    const coinbaseTx = blockData.tx[0];
    const rewardBTC = coinbaseTx.vout.reduce((acc, out) => acc + out.value, 0);

    const transactions = blockData.tx.slice(1).map((tx, index) => {
      // Calculate fee more accurately
      let feeBTC = 0;
      if (tx.fee !== undefined) {
        feeBTC = tx.fee;
      } else {
        
        feeBTC = 0.0001; 
      }

      const size = tx.size || tx.weight || 225; 
      const feeRate = size > 0 ? (feeBTC * 1e8) / size : 0;

      return {
        id: `${blockHash}_tx_${index}`, 
        hash: tx.txid,
        timestamp: new Date(blockData.time * 1000).toISOString(),
        count: index + 1,
        blockId: height.toString(),
        fee: feeBTC, 
        size: size,
        feePaid: feeBTC.toFixed(8), 
        feeRate: Math.round(feeRate),
        inputs: tx.vin.length,
        outputs: tx.vout.length,
      };
    });

    // Step 6: Build block summary
    const blockPayload = {
      type: 'Block_summary',
      data: {
        blockHash: blockData.hash,
        timestamp: new Date(blockData.time * 1000).toISOString(),
        height,
        work: `${(blockData.difficulty / 1e6).toFixed(2)} EH`, 
        txCount: blockData.tx.length,
        reward: rewardBTC, 
        parent: blockData.previousblockhash,
        transactions,
      },
    };

    console.log(`Block ${height} data:`, {
      hash: blockData.hash,
      txCount: blockData.tx.length,
      reward: rewardBTC,
      transactionsCount: transactions.length
    });

    // Send transaction stats
    const totalFees = transactions.reduce((acc, tx) => acc + tx.fee, 0);
    const avgFeeRate = transactions.length > 0 
      ? transactions.reduce((acc, tx) => acc + tx.feeRate, 0) / transactions.length 
      : 0;
    const avgTxSize = transactions.length > 0 
      ? transactions.reduce((acc, tx) => acc + tx.size, 0) / transactions.length 
      : 0;

    const statsPayload = {
      type: 'transaction_stats',
      data: {
        mempoolSize: blockData.tx.length - 1, // Exclude coinbase
        avgFeeRate: avgFeeRate,
        avgTxSize: Math.round(avgTxSize),
        txRate: blockData.tx.length - 1, // Transactions per block
        totalFees: totalFees
      },
    };

    wss.clients.forEach((client) => {
      if (client.readyState === WebSocket.OPEN) {
        client.send(JSON.stringify(blockPayload));
        client.send(JSON.stringify(statsPayload));
      }
    });

    console.log(
      `[WebSocket] Block ${height} sent in ${Date.now() - startTime}ms`
    );
  } catch (err) {
    console.error('[WebSocket] Block fetch failed:', err.message);
  }
}
