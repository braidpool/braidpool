import React, { useEffect, useState } from 'react';
import AdvancedChart from '../AdvancedChart';
import AnimatedStatCard from '../AnimatedStatCard';
import { Activity, ArrowUpRight, Cpu } from 'lucide-react';
import { LatencyPayload } from '../lib/types';
import { LatencyTabProps } from '../lib/types';
export default function LatencyTab({
  isChartLoading,
  chartHovered,
  setChartHovered,
  timeRange,
}: LatencyTabProps) {
  const [chartData, setChartData] = useState<any[]>([]);
  const [averageLatency, setAverageLatency] = useState<string>('0ms');
  const [peakLatency, setPeakLatency] = useState<string>('0ms');
  const [peerCount, setPeerCount] = useState<number>(0);

  useEffect(() => {
    const ws = new WebSocket('ws://localhost:5000');

    ws.onopen = () => {
      console.log('WebSocket connected');
    };

    ws.onmessage = (event) => {
      try {
        const message = JSON.parse(event.data);

        if (message.type === 'latency_update') {
          const incoming: LatencyPayload = message.data;

          const latencyData = (incoming.chartData || []).map((d: any) => ({
            ...d,
            date: new Date(d.date),
            label: new Date(d.date).toLocaleString(),
          }));

          setChartData(latencyData);
          setAverageLatency(
            `${parseFloat(incoming.averageLatency).toFixed(0)}ms`
          );
          setPeakLatency(`${parseFloat(incoming.peakLatency).toFixed(0)}ms`);
          setPeerCount(incoming.peerCount);
        }
      } catch (err) {
        console.error('WebSocket message error:', err);
      }
    };
    ws.onerror = (err) => {
      console.error('WebSocket error:', err);
    };

    ws.onclose = () => {
      console.log('WebSocket disconnected');
    };
    return () => {
      ws?.close();
    };
  }, []);

  return (
    <div className="space-y-6 bg-[#1c1c1c]">
      <div className="flex justify-between items-center ">
        <div>
          <h3 className="text-xl font-bold text-blue-300">Network Latency</h3>

          <p className="text-sm text-gray-400 mt-1">
            Real-time latency measurements
          </p>
        </div>
        <div className="bg-purple-900/30 px-3 py-1 rounded-md">
          <span className="text-purple-300 font-mono">
            AvgLatency : {averageLatency}
          </span>
        </div>
      </div>

      <div
        className="relative border border-gray-800/50 rounded-xl p-6 h-auto bg-[#1c1c1c] backdrop-blur-md overflow-hidden"
        onMouseEnter={() => setChartHovered(true)}
        onMouseLeave={() => setChartHovered(false)}
      >
        <AdvancedChart
          data={chartData}
          height={350}
          isHovered={chartHovered}
          isLoading={isChartLoading}
          timeRange={timeRange}
          primaryLabel="Latency"
          tooltipFormatter={(value, name) => [`${value} ms`, name]}
        />
      </div>

      <div className="grid grid-cols-1 md:grid-cols-3 gap-4">
        <AnimatedStatCard
          title="Average Latency"
          value={averageLatency}
          change="-3%"
          icon={<Activity />}
          delay={0.2}
        />
        <AnimatedStatCard
          title="Peak Latency"
          value={peakLatency}
          change="+15%"
          icon={<ArrowUpRight />}
          delay={0.3}
        />
        <AnimatedStatCard
          title="Nodes Reporting"
          value={peerCount.toString()}
          change="+2"
          icon={<Cpu />}
          delay={0.4}
        />
      </div>
    </div>
  );
}
