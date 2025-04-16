import { useState } from "react"
import { motion } from "framer-motion"
import {
  ChevronDown,
  GitCompare,
} from "lucide-react"
import { MINERS } from "./constants"
import { useComparisonData } from "./Hooks/useComparisonData"
import AdvancedChart from "./AdvancedChart"

interface MinerCompareProps {
  timeRange: string
}

export default function MinerCompare({ timeRange }: MinerCompareProps) {
  const [selectedMiner, setSelectedMiner] = useState<string | null>(null)
  const [chartHovered, setChartHovered] = useState(false)

  const { baseData, comparisonData, isLoading } = useComparisonData(selectedMiner, timeRange)

  return (
    <div className="space-y-6">
      <div className="flex justify-between items-center">
        <div className="flex items-center gap-2">
          <GitCompare className="h-5 w-5 text-blue-400" />
          <h3 className="text-xl font-bold text-blue-300">Miner Comparison</h3>
        </div>

        <div className="relative w-64">
          <select
            className="w-full bg-gray-900/80 border border-gray-700/80 rounded-lg p-2.5 pr-8 appearance-none focus:border-blue-500 focus:ring-2 focus:ring-blue-500/50 transition-all duration-300"
            value={selectedMiner || ""}
            onChange={(e) => setSelectedMiner(e.target.value || null)}
          >
            <option value="">Select a miner to compare</option>
            {MINERS.map((miner) => (
              <option key={miner.id} value={miner.id}>
                {miner.name}
              </option>
            ))}
          </select>
          <div className="absolute inset-y-0 right-0 flex items-center pr-2 pointer-events-none">
            <ChevronDown className="h-4 w-4 text-blue-400" />
          </div>
        </div>
      </div>

      <motion.div
        className="relative border border-gray-800/50 rounded-xl p-6 h-100 bg-black/30 backdrop-blur-md overflow-hidden"
        initial={{ opacity: 0, y: 30, rotateX: 5 }}
        animate={{ opacity: 1, y: 0, rotateX: 0 }}
        transition={{ duration: 0.7, delay: 0.3, type: "spring" }}
        onMouseEnter={() => setChartHovered(true)}
        onMouseLeave={() => setChartHovered(false)}
      >
        <AdvancedChart
          data={baseData}
          comparisonData={selectedMiner ? comparisonData : undefined}
          comparisonLabel={selectedMiner ? MINERS.find((m) => m.id === selectedMiner)?.name || "Comparison" : undefined}
          height={200}
          isHovered={chartHovered}
          isLoading={isLoading}
          timeRange={timeRange}
        />
      </motion.div>

      {!selectedMiner && (
        <motion.div
          className="text-center text-gray-400 py-4"
          initial={{ opacity: 0 }}
          animate={{ opacity: 1 }}
          transition={{ delay: 0.5 }}
        >
          Select a miner above to compare performance with the network average
        </motion.div>
      )}
    </div>
  )
}