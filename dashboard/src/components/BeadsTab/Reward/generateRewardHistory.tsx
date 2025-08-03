import {
  INITIAL_BLOCK_REWARD,
  HALVING_INTERVAL,
  MAX_BLOCKS_HISTORY,
  HISTORY_SAMPLE_RATE,
} from './Constants';

export function generateRewardHistory(blockCount: number) {
  const rewardHistory = [];
  const maxBlocks = Math.min(blockCount, MAX_BLOCKS_HISTORY);
  for (
    let i = Math.max(0, blockCount - maxBlocks);
    i <= blockCount;
    i += Math.max(1, Math.floor(maxBlocks / HISTORY_SAMPLE_RATE))
  ) {
    const blockHalving = Math.floor(i / HALVING_INTERVAL);
    const reward = INITIAL_BLOCK_REWARD / Math.pow(2, blockHalving);
    const item = {
      height: i,
      reward,
      label: `Block ${i}`,
    };
    rewardHistory.push(item);
  }
  return rewardHistory;
}
