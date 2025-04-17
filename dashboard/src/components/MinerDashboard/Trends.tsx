import { useState } from "react"
import { motion } from "framer-motion"
import { Zap, Activity, Database, TrendingUp, ArrowUpRight, Cpu } from "lucide-react"
import AdvancedChart from "./AdvancedChart"
import AnimatedStatCard from "./AnimatedStatCard"
import { useChartData } from "./Hooks/useChartData"
import type { TimeRange, Bead, Transaction } from "./types"

export function TrendsTab({ timeRange }: { timeRange: string }) {
  const [activeSubTab, setActiveSubTab] = useState("hashrate")
  const { data: chartData, isLoading: isChartLoading } = useChartData(timeRange)
  const [chartHovered, setChartHovered] = useState(false)

  return (
    <div className="space-y-8">
      {/* Subtabs */}
      <div className="flex border-b border-gray-800/70 mb-6">
        {[
          { id: "hashrate", label: "Hashrate", icon: <Zap className="w-4 h-4" /> },
          { id: "latency", label: "Latency", icon: <Activity className="w-4 h-4" /> },
          { id: "transactions", label: "Transactions", icon: <Database className="w-4 h-4" /> },
        ].map((tab) => (
          <motion.button
            key={tab.id}
            className={`flex items-center gap-2 px-4 py-3 font-medium relative ${
              activeSubTab === tab.id ? "text-blue-400" : "text-gray-400 hover:text-gray-200"
            }`}
            onClick={() => setActiveSubTab(tab.id)}
            whileHover={{ y: -2 }}
            whileTap={{ scale: 0.97 }}
          >
            {tab.icon}
            {tab.label}
            {activeSubTab === tab.id && (
              <motion.div
                className="absolute bottom-0 left-0 right-0 h-0.5 bg-blue-500"
                layoutId="activeSubTab"
                initial={{ opacity: 0 }}
                animate={{ opacity: 1 }}
                transition={{ type: "spring", stiffness: 300, damping: 30 }}
              />
            )}
          </motion.button>
        ))}
      </div>

      {/* Hashrate subtab */}
      {activeSubTab === "hashrate" && (
        <div className="space-y-6">
          <div className="flex justify-between items-center">
            <div>
              <h3 className="text-xl font-bold text-blue-300">Hashrate (λ)</h3>
              <p className="text-sm text-gray-400 mt-1">Real-time hashrate measurements</p>
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
      )}

      {/* Latency subtab */}
      {activeSubTab === "latency" && (
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
              data={chartData.map((d) => ({ ...d, value: d.value / 2 }))}
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
              color="amber"
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
      )}

      {/* Transactions subtab */}
      {activeSubTab === "transactions" && (
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
              data={chartData.map((d) => ({ ...d, value: d.value * 0.8 }))}
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
              color="amber"
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
      )}
    </div>
  )
}
