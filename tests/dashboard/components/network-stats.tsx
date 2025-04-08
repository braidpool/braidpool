"use client"

import { Loader2 } from "lucide-react"
import { Card, CardContent, CardHeader, CardTitle } from "@/components/ui/card"
import type { NetworkStatsData } from "@/lib/types"

interface NetworkStatsProps {
  data: NetworkStatsData | null
  isLoading: boolean
}

export default function NetworkStats({ data, isLoading }: NetworkStatsProps) {
  if (isLoading) {
    return (
      <>
        {Array.from({ length: 4 }).map((_, i) => (
          <Card key={i} className="bg-gray-900 border-gray-800">
            <CardHeader className="pb-2">
              <CardTitle className="text-sm text-gray-400">Loading...</CardTitle>
            </CardHeader>
            <CardContent>
              <div className="flex items-center justify-center h-12">
                <Loader2 className="h-5 w-5 animate-spin text-gray-600" />
              </div>
            </CardContent>
          </Card>
        ))}
      </>
    )
  }

  if (!data) {
    return (
      <>
        {Array.from({ length: 4 }).map((_, i) => (
          <Card key={i} className="bg-gray-900 border-gray-800">
            <CardHeader className="pb-2">
              <CardTitle className="text-sm text-gray-400">No Data</CardTitle>
            </CardHeader>
            <CardContent>
              <div className="flex items-center justify-center h-12 text-gray-600">--</div>
            </CardContent>
          </Card>
        ))}
      </>
    )
  }

  const stats = [
    {
      title: "Active Nodes",
      value: data.activeNodes.toLocaleString(),
      change: data.nodeChange,
      changeLabel: "from last hour",
    },
    {
      title: "Transactions",
      value: data.transactions.toLocaleString(),
      change: data.transactionChange,
      changeLabel: "from yesterday",
    },
    {
      title: "Pool Hashrate",
      value: `${data.poolHashrate.toFixed(2)} PH/s`,
      change: data.hashrateChange,
      changeLabel: "from last hour",
    },
    {
      title: "Blocks Mined",
      value: data.blocksMined.toLocaleString(),
      change: data.blocksChange,
      changeLabel: "from yesterday",
    },
  ]

  return (
    <>
      {stats.map((stat, i) => (
        <Card key={i} className="bg-gray-900 border-gray-800">
          <CardHeader className="pb-2">
            <CardTitle className="text-sm text-gray-400">{stat.title}</CardTitle>
          </CardHeader>
          <CardContent>
            <div className="text-2xl font-bold text-white">{stat.value}</div>
            <p className={`text-xs mt-1 ${stat.change >= 0 ? "text-green-400" : "text-red-400"}`}>
              {stat.change >= 0 ? "↑" : "↓"} {Math.abs(stat.change).toFixed(1)}% {stat.changeLabel}
            </p>
          </CardContent>
        </Card>
      ))}
    </>
  )
}

