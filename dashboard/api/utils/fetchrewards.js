import { rpcWithEnv } from './rpcWithEnv.js';
import WebSocket from 'ws';

export async function fetchReward(wss) {
  try {
    const startTime = Date.now();
    const blockchainInfo = await rpcWithEnv({ method: 'getblockchaininfo' });

    const blockCount = blockchainInfo.blocks;
    const currentHeight = blockCount;
    let blockReward = 3.125;

    const totalRewards = blockCount * blockReward;
    const rewardRate = blockReward * 144; // Block reward per day

    const payload = {
      type: 'Rewards_update',
      data: {
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
