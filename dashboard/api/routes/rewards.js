import express from 'express';
import { rpcWithEnv } from '../utils/rpcWithEnv.js';

const router = express.Router();

router.get('/', async (req, res) => {
  try {
    const blockchainInfo = await rpcWithEnv({
      
      method: 'getblockchaininfo',
    });
    const blockCount = blockchainInfo.blocks;

    const rewardHistory = [];
    let height = 0;
    const currentHeight = blockCount;
    let blockReward = 3.125;

    const totalRewards = blockCount * blockReward;
    const rewardRate = blockReward * 144; 

    while (height <= currentHeight && blockReward >= 0.00000001) {
      rewardHistory.push({
        height,
        reward: blockReward,
        label: `Block ${height}`,
      });

      for (let i = 1; i < 210000 && height + i <= currentHeight; i += 10000) {
        rewardHistory.push({
          height: height + i,
          reward: blockReward,
          label: `Block ${height + i}`,
        });
      }
      blockReward /= 2;
      height += 210000;
    }

    res.json({
      rewardHistory,
      blockCount,
      blockReward,
      totalRewards,
      rewardRate,
      unit: 'BTC',
    });
  } catch (err) {
    console.error('[Rewards] Error:', err.message);
    res.status(500).json({ error: 'Failed to fetch reward data' });
  }
});

export default router;