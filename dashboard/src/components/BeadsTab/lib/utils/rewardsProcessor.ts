import { RewardsData } from '../types';

export function processRewardsData(data: RewardsData) {
  const { blockCount, blockReward, totalRewards, rewardRate, lastRewardTime, halvings, nextHalving, blocksUntilHalving } = data;
  return {
    blockCount,
    blockReward,
    totalRewards: totalRewards,
    rewardRate,
    lastRewardTime: lastRewardTime ? new Date(lastRewardTime).toISOString() : null,
    unit: 'BTC',
    halvings,
    nextHalving,
    blocksUntilHalving,
  };
} 