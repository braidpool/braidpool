import React from 'react';
import AdvancedChart from '../AdvancedChart';
import AnimatedStatCard from '../AnimatedStatCard';
import { LatencyData } from '../lib/types';

export default function LatencyTab({
  latencyData,
  isLoading,
  timeRange,
}: {
  latencyData: LatencyData;
  isLoading: boolean;
  timeRange: string;
}) {
  const chartData = (latencyData.chartData || []).map((d: any) => ({
    value: d.value,
    date: new Date(d.date),
    label: new Date(d.date).toLocaleTimeString('en-US', {
  hour: '2-digit',
  minute: '2-digit',
  second: '2-digit',
  hour12: true,
  fractionalSecondDigits: 3,
}),
  }));

  return (
    <div className="space-y-6 bg-[#1c1c1c]">
      <div className="flex justify-between items-center">
        <div>
          <h3 className="text-xl font-bold text-blue-300">Network Latency</h3>
          <p className="text-sm text-gray-400 mt-1">
            Real-time latency measurements from peer nodes
          </p>
        </div>
        <div className="bg-purple-900/30 px-3 py-1 rounded-md">
          <span className="text-purple-300 font-mono">
            Avg: {latencyData.averageLatency} | {latencyData.validPings}/{latencyData.peerCount} peers
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
          primaryLabel="Latency (ms)"
          tooltipFormatter={(value, name) => [`${value} ms`, name]}
        />
      </div>

      <div className="grid grid-cols-3 md:grid-cols-3 gap-6">
        <AnimatedStatCard
          title="Average Latency"
          value={latencyData.averageLatency}
        />
        <AnimatedStatCard
          title="Peak Latency"
          value={latencyData.peakLatency}
        />
        <AnimatedStatCard
          title="Active Peers"
          value={`${latencyData.validPings}/${latencyData.peerCount}`}
        />
      </div>
    </div>
  );
}
