import AdvancedChart from '../AdvancedChart';
import AnimatedStatCard from '../AnimatedStatCard';
import { TrendingUp, Zap, Activity } from 'lucide-react';
import React, { useEffect, useState, useRef } from 'react';
import { formatHashrate } from '../lib/utils/formatHashrate';

export default function HashrateTab({
  isChartLoading,
  chartHovered,
  setChartHovered,
  timeRange,
}: any) {
  const [latestStat, setLatestStat] = useState<any>(null);
  const [chartData, setChartData] = useState<any[]>([]);
  const [networkDifficulty, setNetworkDifficulty] = useState<number | null>(
    null
  );
  const ws = useRef<WebSocket | null>(null);

  useEffect(() => {
    ws.current = new WebSocket('ws://localhost:5000');

    ws.current.onopen = () => {
      console.log('WebSocket connected');
    };

    ws.current.onmessage = (event) => {
      try {
        const message = JSON.parse(event.data);

        if (message.type === 'hashrate_update') {
          const { latestStat, networkDifficulty } = message.data;

          setLatestStat(latestStat);
          setNetworkDifficulty(networkDifficulty);

          const formatted = {
            ...latestStat,
            value: latestStat.value / 1e18, // convert to EH/s
            date: new Date(latestStat.date),
            label: new Date(latestStat.date).toLocaleString(),
          };

          setChartData((prev) => {
            const updated = [...prev, formatted];

            return updated.length > 100 ? updated.slice(-100) : updated;
          });
        }
      } catch (err) {
        console.error('Invalid WebSocket message', err);
      }
    };

    ws.current.onerror = (err) => {
      console.error('WebSocket error:', err);
    };

    ws.current.onclose = () => {
      console.log('WebSocket disconnected');
    };

    return () => {
      ws.current?.close();
    };
  }, []);

  const latestValue = chartData.at(-1)?.value || 0;
  const averageHashrate =
    chartData.reduce((acc, d) => acc + d.value, 0) / chartData.length || 0;
  const peakHashrate =
    chartData.reduce((max, d) => Math.max(max, d.value), 0) || 0;

  return (
    <div className="space-y-6 bg-[#1c1c1c]">
      <div className="flex justify-between items-center">
        <div>
          <h3 className="text-xl font-bold text-blue-300">Hashrate (λ)</h3>
          <p className="text-sm text-gray-400 mt-1">
            Real-time hashrate measurements
          </p>
        </div>
        <div className="px-3 py-1 rounded-md">
          <span className="text-blue-300 font-mono">
            λ = {latestValue.toFixed(4)}
          </span>
        </div>
      </div>

      <div
        className="relative border w-full border-gray-800/50 rounded-xl p-6 h-auto backdrop-blur-md overflow-hidden"
        onMouseEnter={() => setChartHovered(true)}
        onMouseLeave={() => setChartHovered(false)}
      >
        <AdvancedChart
          data={chartData}
          height={350}
          isHovered={chartHovered}
          isLoading={isChartLoading}
          timeRange={timeRange}
          primaryLabel="Hashrate "
          tooltipFormatter={(value, name) => [`${value.toFixed(2)} EH/s`, name]}
        />
      </div>

      <div className="grid grid-cols-1 md:grid-cols-3 gap-4">
        <AnimatedStatCard
          title="Average Hashrate"
          value={`${formatHashrate(averageHashrate * 1e18)}`} // convert back to H/s for formatting
          change="+8%"
          icon={<Zap />}
          delay={0.2}
        />
        <AnimatedStatCard
          title="Peak Hashrate"
          value={`${formatHashrate(peakHashrate * 1e18)}`}
          change="+12%"
          icon={<TrendingUp />}
          delay={0.3}
        />
        <AnimatedStatCard
          title="Network Difficulty"
          value={
            typeof networkDifficulty === 'number'
              ? networkDifficulty.toFixed(2)
              : 'Loading...'
          }
          change="+5%"
          icon={<Activity />}
          delay={0.4}
        />
      </div>
    </div>
  );
}
