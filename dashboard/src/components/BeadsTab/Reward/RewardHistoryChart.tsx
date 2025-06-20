import React from 'react';
import AdvancedChart from '../AdvancedChart';
import { RewardHistoryChartProps } from '../lib/types';

const RewardHistoryChart: React.FC<RewardHistoryChartProps> = ({
  rewardHistory,
}) => {
  const chartData = rewardHistory.map((item) => ({
    value: item.reward,
    label: item.label,
    date: new Date(),
    formattedDate: item.label,
  }));

  return (
    <div className="w-full h-auto  text-white rounded-xl shadow-lg p-6">
      <h2 className="text-xl font-bold mb-4  flex items-center gap-2 tracking-tighter">
        Bitcoin Block Reward History
      </h2>
      <AdvancedChart
        data={chartData}
        height={350}
        showControls={true}
        timeRange="all"
        primaryLabel="Reward"
        tooltipFormatter={(value, name) => [`${value} BTC`, name]}
      />
    </div>
  );
};

export default RewardHistoryChart;
