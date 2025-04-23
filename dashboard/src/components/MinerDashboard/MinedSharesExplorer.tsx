import React, { useState, useRef, useEffect } from "react"
import { useTransform, useScroll } from "framer-motion"
import DashboardHeader from "./DashboardHeader"
import { FilterBar } from "./FilterBar/FilterBar"
import EnhancedBlocksTab from "./BlockVisulisation/Block"
import BeadRow from "./MinerRow"

import { BEADS, TRANSACTIONS, BLOCKS } from "./lib/constants"
import { useChartData } from "./Hooks/useChartData"
import { Layers } from "lucide-react"

import { TrendsTab } from "./Trends/TrendsTab"

export default function MinedSharesExplorer() {
  const [expandedBeads, setExpandedBeads] = useState({
    bead1: true,
    bead2: false,
  })
  const [isLoaded, setIsLoaded] = useState(false)
 
  const [activeBead, setActiveBead] = useState<string | null>(null)
  const [activeTab, setActiveTab] = useState("beads")
  const [timeRange, setTimeRange] = useState("month")
  const [error, setError] = useState<string | null>(null)

  // Get chart data with error handling
  const { data: chartData, isLoading: isChartLoading, error: chartError, refetch } = useChartData(timeRange)

  useEffect(() => {
    if (chartError) {
      setError("Failed to load mining data. Please check your connection and try again.")
    } else {
      setError(null)
    }
  }, [chartError])

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

  const handleRetry = () => {
    setError(null)
    refetch?.()
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

        {/* Error state */}
        {error && (
          <div className="bg-red-900/70 border border-red-500/40 text-red-200 rounded-lg p-4 mb-6 flex items-center justify-between">
            <span>{error}</span>
            <button
              onClick={handleRetry}
              className="ml-4 px-4 py-2 bg-red-700 rounded hover:bg-red-600 transition"
            >
              Retry
            </button>
          </div>
        )}

        {/* Main content based on active tab */}
        <div className="relative">
          {!error && activeTab === "beads" && (
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

          {!error && activeTab === "trends" && <TrendsTab timeRange={timeRange} />}

          {!error && activeTab === "blocks" && (
            <div className=" border border-gray-800/50 rounded-xl p-6 bg-black/30 backdrop-blur-md overflow-hidden">
             
              {!error && activeTab === "blocks" && <EnhancedBlocksTab timeRange={timeRange} />}
            </div>
          )}

        </div>
      </div>
    </div>
  )
}