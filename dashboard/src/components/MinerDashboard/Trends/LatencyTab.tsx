import AdvancedChart from "../AdvancedChart"
import AnimatedStatCard from "../AnimatedStatCard"
import { Activity, ArrowUpRight, Cpu } from "lucide-react"

export default function LatencyTab({
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
          <h3 className="text-xl font-bold text-blue-300">Network Latency</h3>
          <p className="text-sm text-gray-400 mt-1">Real-time latency measurements</p>
        </div>
        <div className="bg-purple-900/30 px-3 py-1 rounded-md">
          <span className="text-purple-300 font-mono">120ms</span>
        </div>
      </div>

      <div
        className="relative border border-gray-800/50 rounded-xl p-6 h-110 bg-black/30 backdrop-blur-md overflow-hidden"
        onMouseEnter={() => setChartHovered(true)}
        onMouseLeave={() => setChartHovered(false)}
      >
        <AdvancedChart
          data={chartData.map((d: any) => ({ ...d, value: d.value / 2 }))}
          height={200}
          isHovered={chartHovered}
          isLoading={isChartLoading}
          timeRange={timeRange}
        />
      </div>

      <div className="grid grid-cols-1 md:grid-cols-3 gap-4">
        <AnimatedStatCard
          title="Average Latency"
          value="118ms"
          change="-3%"
          icon={<Activity />}
          color="purple"
          delay={0.2}
        />
        <AnimatedStatCard
          title="Peak Latency"
          value="210ms"
          change="+15%"
          icon={<ArrowUpRight />}
          color="blue"
          delay={0.3}
        />
        <AnimatedStatCard
          title="Nodes Reporting"
          value="24"
          change="+2"
          icon={<Cpu />}
          color="blue"
          delay={0.4}
        />
      </div>
    </div>
  )
}