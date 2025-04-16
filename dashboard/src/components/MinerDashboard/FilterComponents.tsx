
import DateRangePicker from "./DateRangePicker"
import { useState } from "react"
import {motion, AnimatePresence} from "framer-motion"
import { MINERS } from "./constants"
import {
  ChevronDown,
  Calendar,
  Search,
 
  Filter,
  
} from "lucide-react"
interface FilterBarProps {
  timeRange: string
  setTimeRange: (range: string) => void
}

const TIME_RANGES = [
  { label: "Week", value: "week" },
  { label: "Month", value: "month" },
  { label: "Quarter", value: "quarter" },
  { label: "Year", value: "year" },
]
export default function FilterBar({
  timeRange,
  setTimeRange,
}: {
  timeRange: string
  setTimeRange: (range: string) => void
}) {
  const [showFilters, setShowFilters] = useState(false)

  return (
    <motion.div
      className="relative border border-gray-800/50 rounded-xl p-5 mb-8 bg-black/30 backdrop-blur-md shadow-[0_0_25px_rgba(59,130,246,0.15)] overflow-hidden"
      initial={{ opacity: 0, y: 50, scale: 0.9 }}
      animate={{ opacity: 1, y: 0, scale: 1 }}
      transition={{ duration: 0.6, delay: 0.2, type: "spring" }}
    >
      {/* Animated border gradient */}
      <div className="absolute inset-0 p-[1px] rounded-xl overflow-hidden pointer-events-none">
        <motion.div
          className="absolute inset-0 bg-gradient-to-r from-blue-500/30 via-purple-500/30 to-blue-500/30"
          animate={{
            backgroundPosition: ["0% 0%", "200% 0%"],
          }}
          transition={{
            duration: 8,
            repeat: Number.POSITIVE_INFINITY,
            repeatType: "loop",
            ease: "linear",
          }}
        />
      </div>

      <div className="flex flex-col space-y-4">
        <div className="flex justify-between items-center">
          <div className="flex items-center gap-2">
            <Filter className="h-5 w-5 text-blue-400" />
            <h3 className="text-lg font-medium text-white">Filters</h3>
          </div>
          <div className="flex items-center gap-3">
            <DateRangePicker timeRange={timeRange} setTimeRange={setTimeRange} />
            <motion.button
              className="bg-gray-900/50 rounded-lg p-2 text-gray-300 hover:text-white hover:bg-gray-800/70 transition-colors"
              whileHover={{ scale: 1.05 }}
              whileTap={{ scale: 0.95 }}
              onClick={() => setShowFilters(!showFilters)}
            >
              <motion.div animate={{ rotate: showFilters ? 180 : 0 }} transition={{ duration: 0.2 }}>
                <ChevronDown className="h-5 w-5" />
              </motion.div>
            </motion.button>
          </div>
        </div>

        <AnimatePresence>
          {showFilters && (
            <motion.div
              initial={{ height: 0, opacity: 0 }}
              animate={{ height: "auto", opacity: 1 }}
              exit={{ height: 0, opacity: 0 }}
              transition={{ duration: 0.3 }}
              className="overflow-hidden"
            >
              <div className="grid grid-cols-1 md:grid-cols-4 gap-5 pt-4">
                <div>
                  <label className="block mb-2 text-blue-300 font-medium">Miner</label>
                  <div className="relative group">
                    <select className="w-full bg-gray-900/80 border border-gray-700/80 rounded-lg p-2.5 pr-8 appearance-none focus:border-blue-500 focus:ring-2 focus:ring-blue-500/50 transition-all duration-300 group-hover:border-blue-400/70">
                      <option>(All)</option>
                      {MINERS.map((miner) => (
                        <option key={miner.id} value={miner.id}>
                          {miner.name}
                        </option>
                      ))}
                    </select>
                    <div className="absolute inset-y-0 right-0 flex items-center pr-2 pointer-events-none">
                      <motion.div
                        animate={{ y: [0, 2, 0] }}
                        transition={{ duration: 1.5, repeat: Number.POSITIVE_INFINITY, repeatType: "reverse" }}
                      >
                        <ChevronDown className="h-4 w-4 text-blue-400" />
                      </motion.div>
                    </div>
                  </div>
                </div>

                <div>
                  <label className="block mb-2 text-blue-300 font-medium">Start Date</label>
                  <div className="relative group">
                    <input
                      type="date"
                      className="w-full bg-gray-900/80 border border-gray-700/80 rounded-lg p-2.5 pr-8 focus:border-blue-500 focus:ring-2 focus:ring-blue-500/50 transition-all duration-300 group-hover:border-blue-400/70"
                      defaultValue="2021-08-01"
                    />
                    <div className="absolute inset-y-0 right-0 flex items-center pr-2">
                      <motion.div
                        whileHover={{ rotate: 15, scale: 1.1 }}
                        transition={{ type: "spring", stiffness: 300 }}
                      >
                        <Calendar className="h-4 w-4 text-blue-400" />
                      </motion.div>
                    </div>
                  </div>
                </div>

                <div>
                  <label className="block mb-2 text-blue-300 font-medium">End Date</label>
                  <div className="relative group">
                    <input
                      type="date"
                      className="w-full bg-gray-900/80 border border-gray-700/80 rounded-lg p-2.5 focus:border-blue-500 focus:ring-2 focus:ring-blue-500/50 transition-all duration-300 group-hover:border-blue-400/70"
                      defaultValue="2021-09-30"
                    />
                  </div>
                </div>

                <div>
                  <label className="block mb-2 text-blue-300 font-medium">Search</label>
                  <div className="relative group">
                    <input
                      type="text"
                      className="w-full bg-gray-900/80 border border-gray-700/80 rounded-lg p-2.5 pl-9 focus:border-blue-500 focus:ring-2 focus:ring-blue-500/50 transition-all duration-300 group-hover:border-blue-400/70"
                      placeholder="Search transactions, miners..."
                    />
                    <div className="absolute inset-y-0 left-0 flex items-center pl-2.5">
                      <motion.div
                        animate={{ scale: [1, 1.1, 1] }}
                        transition={{ duration: 2, repeat: Number.POSITIVE_INFINITY, repeatType: "reverse" }}
                      >
                        <Search className="h-4 w-4 text-blue-400" />
                      </motion.div>
                    </div>
                  </div>
                </div>
              </div>
            </motion.div>
          )}
        </AnimatePresence>
      </div>
    </motion.div>
  )
}
