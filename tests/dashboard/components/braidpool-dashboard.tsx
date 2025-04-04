"use client"

import { useState, useEffect } from "react"
import BraidVisualization from "./braid-visualization"
import NetworkStats from "./network-stats"
import TransactionMetrics from "./transaction-metrics"
import VisualLogs from "./visual-logs"
import DashboardControls from "./dashboard-controls"
import { Tabs, TabsContent, TabsList, TabsTrigger } from "@/components/ui/tabs"
import { useToast } from "@/hooks/use-toast"
import { fetchBraidData, fetchNetworkStats, fetchTransactionMetrics } from "@/lib/api"
import type { BraidData, NetworkStatsData, TransactionMetricsData, LogEntry } from "@/lib/types"
import { ResizableHandle, ResizablePanel, ResizablePanelGroup } from "@/components/ui/resizable"

export default function BraidpoolDashboard() {
  const [braidData, setBraidData] = useState<BraidData | null>(null)
  const [networkStats, setNetworkStats] = useState<NetworkStatsData | null>(null)
  const [transactionMetrics, setTransactionMetrics] = useState<TransactionMetricsData | null>(null)
  const [logs, setLogs] = useState<LogEntry[]>([])
  const [isLoading, setIsLoading] = useState(true)
  const [error, setError] = useState<string | null>(null)
  const [activeTab, setActiveTab] = useState("visualization")
  const [filterOptions, setFilterOptions] = useState({
    showPoolMinedOnly: false,
    maxCohorts: 10,
    highlightHighestWorkPath: true,
  })

  const { toast } = useToast()

  // Initial data fetch
  useEffect(() => {
    const fetchInitialData = async () => {
      try {
        setIsLoading(true)

        // Fetch all required data
        const [braidData, networkStats, transactionMetrics] = await Promise.all([
          fetchBraidData(),
          fetchNetworkStats(),
          fetchTransactionMetrics(),
        ])

        setBraidData(braidData)
        setNetworkStats(networkStats)
        setTransactionMetrics(transactionMetrics)

        // Add initial log entry
        setLogs([
          {
            timestamp: new Date(),
            message: "Dashboard initialized successfully",
            type: "info",
          },
        ])

        setIsLoading(false)
      } catch (err) {
        setError("Failed to fetch initial data. Please try again.")
        setIsLoading(false)
        toast({
          title: "Error",
          description: "Failed to fetch initial data. Please try again.",
          variant: "destructive",
        })
      }
    }

    fetchInitialData()

    // Set up polling for real-time updates
    const pollingInterval = setInterval(fetchUpdates, 10000) // Poll every 10 seconds

    return () => clearInterval(pollingInterval)
  }, [])

  // Function to fetch updates
  const fetchUpdates = async () => {
    try {
      // Fetch updated data
      const [newBraidData, newNetworkStats, newTransactionMetrics] = await Promise.all([
        fetchBraidData(),
        fetchNetworkStats(),
        fetchTransactionMetrics(),
      ])

      // Check if there are new beads/blocks
      const newBeadCount = newBraidData.beads.length - (braidData?.beads.length || 0)

      if (newBeadCount > 0) {
        // Add log entry for new beads
        setLogs((prevLogs) => [
          {
            timestamp: new Date(),
            message: `${newBeadCount} new transaction${newBeadCount > 1 ? "s" : ""} detected`,
            type: "success",
          },
          ...prevLogs.slice(0, 99), // Keep only the last 100 logs
        ])

        // Show toast notification
        toast({
          title: "New Transactions",
          description: `${newBeadCount} new transaction${newBeadCount > 1 ? "s" : ""} added to the network`,
        })
      }

      // Update state with new data
      setBraidData(newBraidData)
      setNetworkStats(newNetworkStats)
      setTransactionMetrics(newTransactionMetrics)
    } catch (err) {
      // Add error log
      setLogs((prevLogs) => [
        {
          timestamp: new Date(),
          message: "Failed to fetch updates",
          type: "error",
        },
        ...prevLogs.slice(0, 99),
      ])
    }
  }

  // Handle filter changes
  const handleFilterChange = (newFilters: typeof filterOptions) => {
    setFilterOptions(newFilters)

    // Add log entry for filter change
    setLogs((prevLogs) => [
      {
        timestamp: new Date(),
        message: "Visualization filters updated",
        type: "info",
      },
      ...prevLogs.slice(0, 99),
    ])
  }

  // Force manual refresh
  const handleManualRefresh = async () => {
    try {
      setIsLoading(true)
      await fetchUpdates()
      setIsLoading(false)

      toast({
        title: "Refreshed",
        description: "Dashboard data has been refreshed",
      })
    } catch (err) {
      setIsLoading(false)
      toast({
        title: "Error",
        description: "Failed to refresh data",
        variant: "destructive",
      })
    }
  }

  return (
    <div className="container mx-auto p-4 space-y-4">
      <header className="flex justify-between items-center py-4">
        <div>
          <h1 className="text-2xl font-bold text-white">Braidpool Monitoring Dashboard</h1>
          <p className="text-gray-400">Real-time blockchain transaction visualization</p>
        </div>
        <DashboardControls
          filterOptions={filterOptions}
          onFilterChange={handleFilterChange}
          onRefresh={handleManualRefresh}
          isLoading={isLoading}
        />
      </header>

      <div className="grid grid-cols-1 lg:grid-cols-4 gap-4">
        {/* Network Stats Cards */}
        <div className="lg:col-span-4 grid grid-cols-1 md:grid-cols-2 lg:grid-cols-4 gap-4">
          <NetworkStats data={networkStats} isLoading={isLoading} />
        </div>

        {/* Main Content Area with Resizable Panels */}
        <ResizablePanelGroup
          direction="horizontal"
          className="lg:col-span-4 rounded-lg border border-gray-800 bg-gray-950 h-[850px]"
        >
          {/* Main Visualization/Metrics Panel */}
          <ResizablePanel defaultSize={75} minSize={50}>
            <Tabs value={activeTab} onValueChange={setActiveTab} className="w-full h-full">
              <div className="flex justify-between items-center px-4 pt-2">
                <TabsList className="grid grid-cols-2 mb-0">
                  <TabsTrigger value="visualization">Braid Visualization</TabsTrigger>
                  <TabsTrigger value="metrics">Transaction Metrics</TabsTrigger>
                </TabsList>
              </div>

              <TabsContent value="visualization" className="mt-0 h-full">
                <div className="p-4 h-full">
                  {error ? (
                    <div className="flex items-center justify-center h-full text-red-400">{error}</div>
                  ) : (
                    <BraidVisualization data={braidData} isLoading={isLoading} filterOptions={filterOptions} />
                  )}
                </div>
              </TabsContent>

              <TabsContent value="metrics" className="mt-0 h-full">
                <div className="p-4 h-full">
                  <TransactionMetrics data={transactionMetrics} isLoading={isLoading} />
                </div>
              </TabsContent>
            </Tabs>
          </ResizablePanel>

          <ResizableHandle withHandle />

          {/* Sidebar - Logs */}
          <ResizablePanel defaultSize={25} minSize={15}>
            <div className="h-full p-4">
              <h3 className="text-lg font-medium text-white mb-2">Activity Log</h3>
              <p className="text-sm text-gray-400 mb-4">Real-time system events</p>
              <VisualLogs logs={logs} />
            </div>
          </ResizablePanel>
        </ResizablePanelGroup>
      </div>
    </div>
  )
}

