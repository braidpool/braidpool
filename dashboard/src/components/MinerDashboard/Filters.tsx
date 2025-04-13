import { useState } from "react"
import { motion } from "framer-motion"
import { ChevronDown, Calendar, Search } from "lucide-react"

export default function Filters() {
  const [miner, setMiner] = useState("")
  const [timestamp, setTimestamp] = useState("2021-08-01")
  const [transactions, setTransactions] = useState("2021-08-31")
  const [search, setSearch] = useState("")

  return (
    <motion.div
      initial={{ opacity: 0, y: 50, scale: 0.9 }}
      animate={{ opacity: 1, y: 0, scale: 1 }}
      transition={{ duration: 0.6, delay: 0.2, type: "spring" }}
      className="border border-gray-800/50 rounded-xl p-5 mb-8 bg-black/30 backdrop-blur-md shadow-[0_0_25px_rgba(59,130,246,0.15)] relative overflow-hidden"
    >
      {/* Animated gradient border */}
      <div className="absolute inset-0 p-[1px] rounded-xl overflow-hidden pointer-events-none">
        <div className="absolute inset-0 bg-gradient-to-r from-blue-500/30 via-purple-500/30 to-blue-500/30 animate-gradient-x"></div>
      </div>

      <div className="grid grid-cols-1 md:grid-cols-4 gap-5">
        {/* Miner filter */}
        <div>
          <label htmlFor="miner-select" className="block mb-2 text-blue-300 font-medium">Miner</label>
          <div className="relative group">
            <select
              id="miner-select"
              value={miner}
              onChange={(e) => setMiner(e.target.value)}
              className="w-full bg-gray-900/80 border border-gray-700/80 rounded-lg p-2.5 pr-8 appearance-none focus:border-blue-500 focus:ring-2 focus:ring-blue-500/50 transition-all duration-300 group-hover:border-blue-400/70"
            >
              <option value="">(All)</option>
              <option value="miner1">miner1</option>
              <option value="miner2">miner2</option>
              <option value="miner3">miner3</option>
            </select>
            <div className="absolute inset-y-0 right-0 flex items-center pr-2 pointer-events-none">
              <motion.div
                animate={{ y: [0, 2, 0] }}
                transition={{ duration: 1.5, repeat: Infinity, repeatType: "reverse" }}
              >
                <ChevronDown className="h-4 w-4 text-blue-400" />
              </motion.div>
            </div>
            <motion.div
              className="absolute inset-0 rounded-lg bg-blue-500/10 pointer-events-none opacity-0 group-hover:opacity-100"
              initial={false}
              whileHover={{ opacity: 1 }}
              transition={{ duration: 0.2 }}
            />
          </div>
        </div>

        {/* Timestamp filter */}
        <div>
          <label htmlFor="timestamp" className="block mb-2 text-blue-300 font-medium">Timestamp</label>
          <div className="relative group">
            <input
              id="timestamp"
              type="text"
              value={timestamp}
              onChange={(e) => setTimestamp(e.target.value)}
              className="w-full bg-gray-900/80 border border-gray-700/80 rounded-lg p-2.5 pr-8 focus:border-blue-500 focus:ring-2 focus:ring-blue-500/50 transition-all duration-300 group-hover:border-blue-400/70"
            />
            <div className="absolute inset-y-0 right-0 flex items-center pr-2">
              <motion.div whileHover={{ rotate: 15, scale: 1.1 }} transition={{ type: "spring", stiffness: 300 }}>
                <Calendar className="h-4 w-4 text-blue-400" />
              </motion.div>
            </div>
            <motion.div
              className="absolute inset-0 rounded-lg bg-blue-500/10 pointer-events-none opacity-0 group-hover:opacity-100"
              initial={false}
              whileHover={{ opacity: 1 }}
              transition={{ duration: 0.2 }}
            />
          </div>
        </div>

        {/* Transactions filter */}
        <div>
          <label htmlFor="transactions" className="block mb-2 text-blue-300 font-medium">Transactions</label>
          <div className="relative group">
            <input
              id="transactions"
              type="text"
              value={transactions}
              onChange={(e) => setTransactions(e.target.value)}
              className="w-full bg-gray-900/80 border border-gray-700/80 rounded-lg p-2.5 focus:border-blue-500 focus:ring-2 focus:ring-blue-500/50 transition-all duration-300 group-hover:border-blue-400/70"
            />
            <motion.div
              className="absolute inset-0 rounded-lg bg-blue-500/10 pointer-events-none opacity-0 group-hover:opacity-100"
              initial={false}
              whileHover={{ opacity: 1 }}
              transition={{ duration: 0.2 }}
            />
          </div>
        </div>

        {/* Search filter */}
        <div>
          <label htmlFor="search" className="block mb-2 text-blue-300 font-medium">Search...</label>
          <div className="relative group">
            <input
              id="search"
              type="text"
              value={search}
              onChange={(e) => setSearch(e.target.value)}
              className="w-full bg-gray-900/80 border border-gray-700/80 rounded-lg p-2.5 pl-9 focus:border-blue-500 focus:ring-2 focus:ring-blue-500/50 transition-all duration-300 group-hover:border-blue-400/70"
              placeholder="Search..."
            />
            <div className="absolute inset-y-0 left-0 flex items-center pl-2.5">
              <motion.div
                animate={{ scale: [1, 1.1, 1] }}
                transition={{ duration: 2, repeat: Infinity, repeatType: "reverse" }}
              >
                <Search className="h-4 w-4 text-blue-400" />
              </motion.div>
            </div>
            <motion.div
              className="absolute inset-0 rounded-lg bg-blue-500/10 pointer-events-none opacity-0 group-hover:opacity-100"
              initial={false}
              whileHover={{ opacity: 1 }}
              transition={{ duration: 0.2 }}
            />
          </div>
        </div>
      </div>
    </motion.div>
  )
}
