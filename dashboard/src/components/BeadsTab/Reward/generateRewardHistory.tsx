export function generateRewardHistory(
  blockCount: number,
  initialReward: number = 3.125
) {
  const rewardHistory = [];
  let height = 0;
  let reward = initialReward;

  while (height <= blockCount && reward >= 0.00000001) {
    rewardHistory.push({
      height,
      reward,
      label: `Block ${height}`,
    });

    for (let i = 1; i < 210000 && height + i <= blockCount; i += 10000) {
      rewardHistory.push({
        height: height + i,
        reward,
        label: `Block ${height + i}`,
      });
    }

    reward /= 2;
    height += 210000;
  }

  return rewardHistory;
}
