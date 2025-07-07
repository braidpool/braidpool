import React from 'react';
import AdvancedChart from '../AdvancedChart';
import { RewardHistoryChartProps } from '../lib/Types';

const RewardHistoryChart: React.FC<RewardHistoryChartProps> = ({
  rewardHistory,
}) => {
  const chartData = rewardHistory
    .map((item) => {
      if (
        !item ||
        typeof item.height !== 'number' ||
        typeof item.reward !== 'number'
      ) {
        return null;
      }
      return {
        value: item.reward,
        timestamp: item.height,
      };
    })
    .filter((d): d is { value: number; timestamp: number } => d !== null);

  if (chartData.length === 0) {
    return (
      <div className="w-full h-auto text-white rounded-xl shadow-lg p-6">
        <h2 className="text-xl font-bold mb-4 tracking-tighter">
          Bitcoin Block Reward
        </h2>
        <div className="h-64 flex items-center justify-center text-gray-400">
          No reward history data available
        </div>
      </div>
    );
  }

  return (
    <div className="w-full h-auto text-white rounded-xl shadow-lg p-6">
      <h2 className="text-xl font-bold mb-4 tracking-tighter">
        Bitcoin Block Reward
      </h2>
      <AdvancedChart
        data={chartData}
        yLabel="Block Reward"
        unit="BTC"
        lineColor="#8884d8"
      />
    </div>
  );
};

export default RewardHistoryChart;
