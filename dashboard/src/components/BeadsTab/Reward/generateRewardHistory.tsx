export function generateRewardHistory(blockCount: number) {
  const rewardHistory = [];
  const maxBlocks = Math.min(blockCount, 1000);
  for (
    let i = Math.max(0, blockCount - maxBlocks);
    i <= blockCount;
    i += Math.max(1, Math.floor(maxBlocks / 50))
  ) {
    const blockHalving = Math.floor(i / 210000);
    const reward = 50 / Math.pow(2, blockHalving);
    const item = {
      height: i,
      reward,
      label: `Block ${i}`,
    };
    rewardHistory.push(item);
  }
  return rewardHistory;
}
