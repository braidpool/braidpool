import AdvancedChart from '../AdvancedChart';
import AnimatedStatCard from '../AnimatedStatCard';
import { TrendingUp, Zap, Activity } from 'lucide-react';
import React, { useEffect, useState, useRef } from 'react';
import { formatHashrate } from '../lib/formatHashrate';
export default function HashrateTab({
  isChartLoading,
  chartHovered,
  setChartHovered,
  timeRange,
}: any) {
  const [stats, setStats] = useState<any>(null);
  const [chartData, setChartData] = useState<any>([]);
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
          const incoming = message.data;

          setStats(incoming);

          const formattedChart = (incoming.chartData || []).map((d: any) => ({
            ...d,
            value: (d.value / 1e18 ),
            date: new Date(d.date),
            label: new Date(d.date).toLocaleString(),
          }));

          setChartData(formattedChart);
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
            λ ={' '}
            {stats
              ? `${(stats.chartData?.at(-1)?.value / 1e12).toFixed(4)}`
              : '...'}
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
          value={
            stats
              ? `${formatHashrate(stats.averageHashrate )} `
              : 'Loading...'
          }
          change="+8%"
          icon={<Zap />}
          delay={0.2}
        />
        <AnimatedStatCard
          title="Peak Hashrate"
          value={
            stats ? `${formatHashrate(stats.peakHashrate )} ` : 'Loading...'
          }
          change="+12%"
          icon={<TrendingUp />}
          delay={0.3}
        />
        <AnimatedStatCard
          title="Network Difficulty"
          value={
            stats
              ? `${parseFloat(stats.networkDifficulty).toFixed(2)}`
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
