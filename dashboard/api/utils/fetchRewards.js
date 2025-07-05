import { rpcWithEnv } from './rpcWithEnv.js';
import WebSocket from 'ws';

export async function fetchReward(wss) {
  try {
    const blockchainInfo = await rpcWithEnv({ method: 'getblockchaininfo' });
    const blockCount = blockchainInfo.blocks;

    const halvings = Math.floor(blockCount / 210000);
    const blockReward = 50 / Math.pow(2, halvings);

    let totalRewards = 0;
    let remainingBlocks = blockCount;
    let reward = 50;
    let halvingHeight = 210000;
    while (remainingBlocks > 0 && reward > 0) {
      const blocksThisEra = Math.min(remainingBlocks, halvingHeight);
      totalRewards += blocksThisEra * reward;
      remainingBlocks -= blocksThisEra;
      reward /= 2;
    }
    const rewardRate = blockReward * 144;

    let lastRewardTime = null;
    try {
      const recentBlock = await rpcWithEnv({
        method: 'getblock',
        params: [blockchainInfo.bestblockhash, 1],
      });
      lastRewardTime = recentBlock.time * 1000;
    } catch (err) {
      console.warn('[Rewards] Could not fetch recent block info:', err.message);
    }

    const payload = {
      type: 'rewards_data',
      data: {
        blockCount,
        blockReward,
        totalRewards,
        rewardRate,
        lastRewardTime,
        halvings,
        nextHalving: (halvings + 1) * 210000,
        blocksUntilHalving: (halvings + 1) * 210000 - blockCount,
      },
    };

    wss.clients.forEach((client) => {
      if (client.readyState === WebSocket.OPEN) {
        client.send(JSON.stringify(payload));
      }
    });
  } catch (err) {
    console.error('[Rewards] Failed to fetch/send reward data:', err.message);
  }
}
