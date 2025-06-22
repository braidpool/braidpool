import React from 'react';
import AdvancedChart from '../AdvancedChart';
import { RewardHistoryChartProps } from '../lib/types';
import { formatBlockLabel } from '../lib/utils/utils';

const RewardHistoryChart: React.FC<RewardHistoryChartProps> = ({
  rewardHistory,
}) => {
  console.log('RewardHistoryChart data:', rewardHistory);
  
  const chartData = rewardHistory.map((item, index) => {
    if (!item || typeof item.height !== 'number' || typeof item.reward !== 'number') {
      console.warn('Invalid reward history item:', item);
      return {
        value: 0,
        label: `Block ${index}`,
        date: new Date(),
        formattedDate: `Block ${index}`,
      };
    }
    
    const label = item.label || formatBlockLabel(item.height);
    console.log('Chart item:', { height: item.height, label, reward: item.reward });
    
    return {
      value: item.reward,
      label: label,
      date: new Date(),
      formattedDate: label,
    };
  }).filter(Boolean);

  console.log('Final chart data:', chartData);

  if (chartData.length === 0) {
    return (
      <div className="w-full h-auto text-white rounded-xl shadow-lg p-6">
        <h2 className="text-xl font-bold mb-4 flex items-center gap-2 tracking-tighter">
          Bitcoin Block Reward History (Block-based)
        </h2>
        <div className="h-64 flex items-center justify-center text-gray-400">
          No reward history data available
        </div>
      </div>
    );
  }

  return (
    <div className="w-full h-auto  text-white rounded-xl shadow-lg p-6">
      <h2 className="text-xl font-bold mb-4  flex items-center gap-2 tracking-tighter">
        Bitcoin Block Reward History (Block-based)
      </h2>
      <AdvancedChart
        data={chartData}
        height={350}
        showControls={true}
        timeRange="all"
        primaryLabel="Reward (BTC)"
        tooltipFormatter={(value, name) => [`${value} BTC`, name]}
      />
    </div>
  );
};

export default RewardHistoryChart;
