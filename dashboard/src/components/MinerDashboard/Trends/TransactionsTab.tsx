import AdvancedChart from "../AdvancedChart"
import AnimatedStatCard from "../AnimatedStatCard"
import { Database, TrendingUp, Activity } from "lucide-react"

export default function TransactionsTab({
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
          <h3 className="text-xl font-bold text-blue-300">Transaction Activity</h3>
          <p className="text-sm text-gray-400 mt-1">Mempool transaction statistics</p>
        </div>
        <div className="bg-emerald-900/30 px-3 py-1 rounded-md">
          <span className="text-emerald-300 font-mono">42 tx/min</span>
        </div>
      </div>

      <div
        className="relative border border-gray-800/50 rounded-xl p-6 h-110 bg-black/30 backdrop-blur-md overflow-hidden"
        onMouseEnter={() => setChartHovered(true)}
        onMouseLeave={() => setChartHovered(false)}
      >
        <AdvancedChart
          data={chartData.map((d: any) => ({ ...d, value: d.value * 0.8 }))}
          height={200}
          isHovered={chartHovered}
          isLoading={isChartLoading}
          timeRange={timeRange}
        />
      </div>

      <div className="grid grid-cols-1 md:grid-cols-3 gap-4">
        <AnimatedStatCard
          title="Mempool Size"
          value="124 tx"
          change="+18"
          icon={<Database />}
          color="emerald"
          delay={0.2}
        />
        <AnimatedStatCard
          title="Avg Fee Rate"
          value="11.2 sats/vB"
          change="+2.1"
          icon={<TrendingUp />}
          color="purple"
          delay={0.3}
        />
        <AnimatedStatCard
          title="Avg Tx Size"
          value="845 vB"
          change="-12"
          icon={<Activity />}
          color="blue"
          delay={0.4}
        />
      </div>
    </div>
  )
}