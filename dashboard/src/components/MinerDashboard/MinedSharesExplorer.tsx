import React, { useState, useRef, useEffect } from "react"
import { useTransform, useScroll } from "framer-motion"
import DashboardHeader from "./DashboardHeader"
import { FilterBar } from "./FilterComponents"

import BeadRow from "./MinerRow"


import { BEADS, TRANSACTIONS, BLOCKS } from "./constants"
import { useChartData } from "./Hooks/useChartData"
import { Layers } from "lucide-react"

import { TrendsTab } from "./Trends"
export default function MinedSharesExplorer() {
  const [expandedBeads, setExpandedBeads] = useState({
    bead1: true,
    bead2: false,
  })
  const [isLoaded, setIsLoaded] = useState(false)
  const [chartHovered, setChartHovered] = useState(false)
  const [activeBead, setActiveBead] = useState<string | null>(null)
  const [activeTab, setActiveTab] = useState("beads")
  const [timeRange, setTimeRange] = useState("month")

  // Get chart data
  const { data: chartData, isLoading: isChartLoading } = useChartData(timeRange)

  // Refs for scroll animations
  const containerRef = useRef(null)
  const { scrollYProgress } = useScroll({ target: containerRef })
  const headerOpacity = useTransform(scrollYProgress, [0, 0.1], [1, 0.8])
  const headerScale = useTransform(scrollYProgress, [0, 0.1], [1, 0.95])

  // Simulate loading data
  useEffect(() => {
    const timer = setTimeout(() => {
      setIsLoaded(true)
    }, 1000)

    return () => clearTimeout(timer)
  }, [])

  const toggleBead = (bead: string) => {
    setExpandedBeads((prev) => ({
      ...prev,
      [bead]: !prev[bead],
    }))
    setActiveBead(bead)

    // Reset active bead after animation
    setTimeout(() => {
      setActiveBead(null)
    }, 1000)
  }

  const handleParentClick = (parentHash: string) => {
    // Find the bead with this hash
    const bead = BEADS.find((b) => b.name === parentHash)
    if (bead) {
      toggleBead(bead.id)
    }
  }

  return (
    <div
      ref={containerRef}
      className="min-h-screen bg-gradient-to-br from-gray-900 via-[#0a0b1e] to-black text-white overflow-hidden relative perspective-1000"
    >
      {/* Main content container */}
      <div className="relative z-10 container mx-auto px-4 py-8">
        {/* Header with parallax effect */}
        <DashboardHeader
          headerOpacity={headerOpacity}
          headerScale={headerScale}
          activeTab={activeTab}
          setActiveTab={setActiveTab}
        />

        {/* Filters */}
        <FilterBar timeRange={timeRange} setTimeRange={setTimeRange} />

        {/* Main content based on active tab */}
        <div className="relative">
          {activeTab === "beads" && (
            <div className="space-y-8">
              {/* Data Table */}
              <div className="relative border border-gray-800/50 rounded-xl mb-8 bg-black/30 backdrop-blur-md shadow-[0_0_25px_rgba(59,130,246,0.15)] overflow-hidden transform-gpu">
                {/* Table header */}
                <div className="grid grid-cols-4 p-4 border-b border-gray-800/80 font-medium relative overflow-hidden">
                  <div className="text-blue-200 font-semibold relative z-10">Bead Hash</div>
                  <div className="text-blue-200 font-semibold relative z-10">Timestamp</div>
                  <div className="text-blue-200 font-semibold relative z-10">Difficulty</div>
                  <div className="text-blue-200 font-semibold relative z-10">Transactions</div>
                </div>

                {/* Loading shimmer effect */}
                {!isLoaded && (
                  <div className="p-8">
                    <div className="h-12 bg-gray-800/50 rounded-md animate-pulse mb-4"></div>
                    <div className="h-12 bg-gray-800/50 rounded-md animate-pulse"></div>
                  </div>
                )}

                {isLoaded && (
                  <>
                    {BEADS.map((bead) => (
                      <BeadRow
                        key={bead.id}
                        bead={bead}
                        isExpanded={expandedBeads[bead.id] || false}
                        onToggle={toggleBead}
                        isActive={activeBead === bead.id}
                        transactions={TRANSACTIONS[bead.id] || []}
                        onParentClick={handleParentClick}
                      />
                    ))}
                  </>
                )}
              </div>
            </div>
          )}

          {activeTab === "trends" && <TrendsTab timeRange={timeRange} />}

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
                {BLOCKS.map((block, i) => (
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

        </div>
      </div>
    </div>
  )
}