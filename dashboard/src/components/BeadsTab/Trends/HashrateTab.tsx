import AdvancedChart from '../AdvancedChart';
import AnimatedStatCard from '../AnimatedStatCard';
import { TrendingUp, Zap, Activity } from 'lucide-react';

export default function HashrateTab({
  chartData,
  isChartLoading,
  chartHovered,
  setChartHovered,
  timeRange,
}: any) {
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
          <span className="text-blue-300 font-mono">λ = 0.0024</span>
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
          value="0.0022 λ"
          change="+8%"
          icon={<Zap />}
          color="blue"
          delay={0.2}
        />
        <AnimatedStatCard
          title="Peak Hashrate"
          value="0.0031 λ"
          change="+12%"
          icon={<TrendingUp />}
          color="emerald"
          delay={0.3}
        />
        <AnimatedStatCard
          title="Network Difficulty"
          value="11.4"
          change="+5%"
          icon={<Activity />}
          color="purple"
          delay={0.4}
        />
      </div>
    </div>
  );
}
