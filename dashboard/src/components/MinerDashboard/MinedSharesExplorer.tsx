import { useState, useRef, useEffect } from "react"
import { useTransform, useScroll } from "framer-motion"
import DashboardHeader from "./DashboardHeader"
import FilterBar from "./FilterComponents"
import MinerRow from "./MinerRow"
import AnimatedStatCard from "./AnimatedStatCard"
import MinerCompare from "./MinerCompare"
import { MINERS, TRANSACTIONS, BLOCKS } from "./constants"
import { useChartData } from "./Hooks/useChartData"
import { Activity, Layers, Cpu } from "lucide-react"
import AdvancedChart from "./AdvancedChart"

export default function MinedSharesExplorer() {
  const [expandedMiners, setExpandedMiners] = useState<{ [key: string]: boolean }>({
    miner1: true,
    miner2: false,
  })
  const [isLoaded, setIsLoaded] = useState(false)
  const [chartHovered, setChartHovered] = useState(false)
  const [activeMiner, setActiveMiner] = useState<string | null>(null)
  const [activeTab, setActiveTab] = useState("miners")
  const [timeRange, setTimeRange] = useState("month")

  const { data: chartData, isLoading: isChartLoading } = useChartData(timeRange)

  const containerRef = useRef(null)
  const { scrollYProgress } = useScroll({ target: containerRef })
  const headerOpacity = useTransform(scrollYProgress, [0, 0.1], [1, 0.8])
  const headerScale = useTransform(scrollYProgress, [0, 0.1], [1, 0.95])

  useEffect(() => {
    const timer = setTimeout(() => {
      setIsLoaded(true)
    }, 1000)
    return () => clearTimeout(timer)
  }, [])

  const toggleMiner = (miner: string) => {
    setExpandedMiners((prev) => ({
      ...prev,
      [miner]: !prev[miner],
    }))
    setActiveMiner(miner)
    setTimeout(() => {
      setActiveMiner(null)
    }, 1000)
  }

  return (
    <div
      ref={containerRef}
      className="min-h-screen bg-gradient-to-br from-gray-900 via-[#0a0b1e] to-black text-white overflow-hidden relative perspective-1000"
    >
      <div className="relative z-10 container mx-auto px-4 py-8">
        <DashboardHeader
          headerOpacity={headerOpacity}
          headerScale={headerScale}
          activeTab={activeTab}
          setActiveTab={setActiveTab}
        />

        <FilterBar timeRange={timeRange} setTimeRange={setTimeRange} />

        <div className="relative">
          {activeTab === "miners" && (
            <div className="space-y-8">
              <div className="relative border border-gray-800/50 rounded-xl mb-8 bg-black/30 backdrop-blur-md shadow-[0_0_25px_rgba(59,130,246,0.15)] overflow-hidden transform-gpu">
                <div className="grid grid-cols-3 p-4 border-b border-gray-800/80 font-medium relative overflow-hidden">
                  <div className="text-blue-200 font-semibold relative z-10">Miner</div>
                  <div className="text-blue-200 font-semibold relative z-10">Timestamp</div>
                  <div className="text-blue-200 font-semibold relative z-10">Transactions</div>
                </div>
                {!isLoaded && (
                  <div className="p-8">
                    <div className="h-12 bg-gray-800/50 rounded-md animate-pulse mb-4"></div>
                    <div className="h-12 bg-gray-800/50 rounded-md animate-pulse"></div>
                  </div>
                )}
                {isLoaded && (
                  <>
                    {MINERS.map((miner) => (
                      <MinerRow
                        key={miner.id}
                        miner={miner}
                        isExpanded={expandedMiners[miner.id] || false}
                        onToggle={toggleMiner}
                        isActive={activeMiner === miner.id}
                        transactions={TRANSACTIONS[miner.id] || []}
                      />
                    ))}
                  </>
                )}
              </div>
            </div>
          )}

          {activeTab === "trends" && (
            <div className="space-y-8">
              <div
                className="relative border border-gray-800/50 rounded-xl p-6 h-80 bg-black/30 backdrop-blur-md overflow-hidden"
                onMouseEnter={() => setChartHovered(true)}
                onMouseLeave={() => setChartHovered(false)}
              >
                <div className="flex justify-between items-center mb-6">
                  <div>
                    <h3 className="text-xl font-bold text-blue-300">Mining Activity</h3>
                    <p className="text-sm text-gray-400 mt-1">
                      {chartData.length > 0 &&
                        `Data from ${chartData[0].formattedDate} to ${chartData[chartData.length - 1].formattedDate}`}
                    </p>
                  </div>
                  <div className="flex items-center gap-4">
                    <div className="flex items-center gap-2">
                      <div className="w-3 h-3 rounded-full bg-blue-500"></div>
                      <span className="text-sm text-gray-300">Transactions</span>
                    </div>
                    <div className="flex items-center gap-2">
                      <div className="w-3 h-3 rounded-full bg-purple-500"></div>
                      <span className="text-sm text-gray-300">Blocks</span>
                    </div>
                  </div>
                </div>
                <AdvancedChart
                  data={chartData}
                  height={200}
                  isHovered={chartHovered}
                  isLoading={isChartLoading}
                  timeRange={timeRange}
                />
              </div>
              <div className="grid grid-cols-1 md:grid-cols-3 gap-4 mt-6">
                <AnimatedStatCard
                  title="Total Miners"
                  value="124"
                  change="+12%"
                  icon={<Cpu />}
                  color="blue"
                  delay={0.4}
                />
                <AnimatedStatCard
                  title="Avg. Transactions"
                  value="1,432"
                  change="+8%"
                  icon={<Activity />}
                  color="purple"
                  delay={0.5}
                />
                <AnimatedStatCard
                  title="Total Blocks"
                  value="8,901"
                  change="+15%"
                  icon={<Layers />}
                  color="emerald"
                  delay={0.6}
                />
              </div>
            </div>
          )}

          {activeTab === "blocks" && (
            <div className="relative border border-gray-800/50 rounded-xl p-6 bg-black/30 backdrop-blur-md overflow-hidden">
              <div className="flex justify-between items-center mb-4">
                <div>
                  <h3 className="text-xl font-bold text-blue-300">Recent Blocks</h3>
                  <p className="text-sm text-gray-400 mt-1">
                    {timeRange === "week" && "Blocks mined in the last 7 days"}
                    {timeRange === "month" && "Blocks mined in the last 30 days"}
                    {timeRange === "quarter" && "Blocks mined in the last 90 days"}
                    {timeRange === "year" && "Blocks mined in the last 365 days"}
                  </p>
                </div>
              </div>
              <div className="space-y-4">
                {BLOCKS.map((block) => (
                  <div
                    key={block.id}
                    className="bg-gray-900/50 p-4 rounded-lg flex justify-between items-center hover:bg-gray-800/50 transition-colors duration-300"
                  >
                    <div className="flex items-center gap-3">
                      <div className="bg-blue-500/20 p-2 rounded-lg">
                        <Layers className="h-5 w-5 text-blue-400" />
                      </div>
                      <div>
                        <h4 className="font-medium text-white">Block #{block.id}</h4>
                        <p className="text-sm text-gray-400">Mined by {block.miner}</p>
                      </div>
                    </div>
                    <div className="text-right">
                      <p className="text-purple-300 font-medium">{block.transactions} Transactions</p>
                      <p className="text-sm text-gray-400">{block.timestamp}</p>
                    </div>
                  </div>
                ))}
              </div>
            </div>
          )}

          {activeTab === "compare" && <MinerCompare timeRange={timeRange} />}
        </div>
      </div>
    </div>
  )
}
