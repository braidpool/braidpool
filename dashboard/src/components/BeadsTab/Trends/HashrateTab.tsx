import React from 'react';
import AdvancedChart from '../AdvancedChart';
import AnimatedStatCard from '../AnimatedStatCard';
import { HashrateData } from '../lib/types';

export default function HashrateTab({
  hashrateData,
  isLoading,
  timeRange,
}: {
  hashrateData: HashrateData;
  isLoading: boolean;
  timeRange: string;
}) {
  const chartData = (hashrateData.history || []).map((d: any) => ({
    value: parseFloat(d.value) || 0,
    date: new Date(d.date),
    label: new Date(d.date).toLocaleTimeString(),
  }));

  return (
    <div className="space-y-6 bg-[#1c1c1c]">
      <div className="flex justify-between items-center">
        <div>
          <h3 className="text-xl font-bold text-blue-300">Pool Hashrate</h3>
          <p className="text-sm text-gray-400 mt-1">
            Live hashrate of the Braidpool
          </p>
        </div>
        <div className="bg-emerald-900/30 px-3 py-1 rounded-md">
          <span className="text-emerald-300 font-mono">
            {hashrateData.current}
          </span>
        </div>
      </div>

      <div
        className="relative border border-gray-800/50 rounded-xl p-6 h-auto bg-[#1c1c1c] backdrop-blur-md overflow-hidden"
      >
        <AdvancedChart
          data={chartData}
          height={350}
          isLoading={isLoading}
          timeRange={timeRange}
          primaryLabel="Hashrate (EH/s)"
          tooltipFormatter={(value) => [`${value} EH/s`, 'Hashrate']}
        />
      </div>

      <div className="grid grid-cols-3 md:grid-cols-3 sm:grid-cols-1  gap-6">
        <AnimatedStatCard
          title="Current Hashrate"
          value={hashrateData.current}
        />
        <AnimatedStatCard
          title="Peak Hashrate (24h)"
          value={hashrateData.peak}
        />
        <AnimatedStatCard
          title="Network Difficulty"
          value={hashrateData.networkDifficulty.toExponential(2)}
        />
      </div>
    </div>
  );
}
