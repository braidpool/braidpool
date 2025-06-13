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
      <h2 className="text-2xl font-bold mb-4  flex items-center gap-2">
        <svg width="28" height="28" fill="none" viewBox="0 0 24 24">
          <circle cx="12" cy="12" r="10" fill="#06b6d4" opacity="0.2" />
          <path
            d="M12 6v6l4 2"
            stroke="#06b6d4"
            strokeWidth="2"
            strokeLinecap="round"
            strokeLinejoin="round"
          />
        </svg>
        Bitcoin Block Reward History
      </h2>
      <AdvancedChart
        data={chartData}
        height={350}
        showControls={true}
        timeRange="all"
      />
    </div>
  );
};

export default RewardHistoryChart;
