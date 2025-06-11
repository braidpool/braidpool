import AdvancedChart from '../AdvancedChart';
import AnimatedStatCard from '../AnimatedStatCard';
import { TrendingUp, Zap, Activity } from 'lucide-react';
import React, { useEffect, useState } from 'react';

export default function HashrateTab({
  isChartLoading,
  chartHovered,
  setChartHovered,
  timeRange,
}: any) {
  const [stats, setStats] = useState<any>(null);
  const [chartData, setChartData] = useState<any>([]);

  useEffect(() => {
    const fetchStats = async () => {
      try {
        const res = await fetch('http://localhost:3001/api/stats');
        const data = await res.json();
        setStats(data);
        // Ensure date is a Date object
        const chartData = (data.chartData || []).map((d: any) => ({
          ...d,
          date: new Date(d.date),
          label: new Date(d.date).toLocaleString(),
        }));
        setChartData(chartData);
      } catch (err) {
        setStats(null);
        setChartData([]);
      }
    };

    fetchStats();
    const interval = setInterval(fetchStats, 60000);

    return () => clearInterval(interval);
  }, []);

  return (
    <div className="space-y-6">
      <div className="flex justify-between items-center">
        <div>
          <h3 className="text-xl font-bold text-blue-300">Hashrate (λ)</h3>
          <p className="text-sm text-gray-400 mt-1">
            Real-time hashrate measurements
          </p>
        </div>
        <div className="bg-blue-900/30 px-3 py-1 rounded-md">
          <span className="text-blue-300 font-mono">
            {' '}
            λ ={' '}
            {stats
              ? `${(stats.chartData.at(-1)?.value / 1e12).toFixed(4)}`
              : '...'}
          </span>
        </div>
      </div>

      <div
        className="relative border w-full border-gray-800/50 rounded-xl p-6 h-110 bg-black/30 backdrop-blur-md overflow-hidden"
        onMouseEnter={() => setChartHovered(true)}
        onMouseLeave={() => setChartHovered(false)}
      >
        <AdvancedChart
          data={chartData}
          height={200}
          isHovered={chartHovered}
          isLoading={isChartLoading}
          timeRange={timeRange}
        />
      </div>

      <div className="grid grid-cols-1 md:grid-cols-3 gap-4">
        <AnimatedStatCard
          title="Average Hashrate"
          value={
            stats
              ? `${(stats.averageHashrate / 1e12).toFixed(2)} λ`
              : 'Loading...'
          }
          change="+8%"
          icon={<Zap />}
          delay={0.2}
        />
        <AnimatedStatCard
          title="Peak Hashrate"
          value={
            stats ? `${(stats.peakHashrate / 1e12).toFixed(4)} λ` : 'Loading...'
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
