import { rpcWithEnv } from './rpcWithEnv.js';
import WebSocket from 'ws';

export async function fetchReward(wss) {
  try {
    const startTime = Date.now();
    const blockchainInfo = await rpcWithEnv({ method: 'getblockchaininfo' });
    const blockCount = blockchainInfo.blocks;
    
    const halvings = Math.floor(blockCount / 210000);
    const blockReward = 50 / Math.pow(2, halvings);
    
    const totalRewards = blockCount * blockReward;
    const rewardRate = blockReward * 144; 
  
    let lastRewardTime = '';
    try {
      const recentBlock = await rpcWithEnv({
        method: 'getblock',
        params: [blockchainInfo.bestblockhash, 1]
      });
      lastRewardTime = new Date(recentBlock.time * 1000).toISOString();
    } catch (err) {
      console.warn('[Rewards] Could not fetch recent block info:', err.message);
    }

    const payload = {
      type: 'Rewards_update',
      data: {
        blockCount,
        blockReward,
        totalRewards,
        rewardRate,
        lastRewardTime,
        unit: 'BTC',
        halvings,
        nextHalving: (halvings + 1) * 210000,
        blocksUntilHalving: ((halvings + 1) * 210000) - blockCount,
      },
    };

    wss.clients.forEach((client) => {
      if (client.readyState === WebSocket.OPEN) {
        client.send(JSON.stringify(payload));
      }
    });

    console.log(
      `[Rewards] Sent rewards update in ${Date.now() - startTime}ms - Block ${blockCount}, Reward: ${blockReward} BTC`
    );
  } catch (err) {
    console.error('[Rewards] Failed to fetch/send reward data:', err.message);
  }
}
