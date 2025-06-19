import { rpcWithEnv } from './rpcWithEnv.js';
import WebSocket from 'ws';

export async function fetchReward(wss) {
  try {
    const startTime = Date.now();
    const blockchainInfo = await rpcWithEnv({ method: 'getblockchaininfo' });

    const blockCount = blockchainInfo.blocks;
    const currentHeight = blockCount;
    let blockReward = 3.125;

    const rewardHistory = [];
    let height = 0;

    const totalRewards = blockCount * blockReward;
    const rewardRate = blockReward * 144; // Block reward per day

    console.log(`Generating reward history up to block ${currentHeight}`);

    while (height <= currentHeight && blockReward >= 0.00000001) {
      rewardHistory.push({
        height,
        reward: blockReward,
        label: `Block ${height}`,
      });

      for (let i = 1; i < 210000 && height + i <= currentHeight; i += 10000) {
        const block = height + i;
        rewardHistory.push({
          height: block,
          reward: blockReward,
          label: `Block ${block}`,
        });
      }

      blockReward /= 2;
      height += 210000;
    }

    const payload = {
      type: 'Rewards_update',
      data: {
        rewardHistory,
        blockCount,
        blockReward,
        totalRewards,
        rewardRate,
        unit: 'BTC',
      },
    };

    wss.clients.forEach((client) => {
      if (client.readyState === WebSocket.OPEN) {
        client.send(JSON.stringify(payload));
      }
    });

    console.log(
      `Sent rewards update to clients in ${Date.now() - startTime}ms`
    );
  } catch (err) {
    console.error('[WebSocket] Failed to fetch/send reward data:', err.message);
  }
}
