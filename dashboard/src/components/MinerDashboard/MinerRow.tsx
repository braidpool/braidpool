

import { motion, AnimatePresence} from "framer-motion"
import {
  ChevronDown,
  
  Zap,

} from "lucide-react"

import TransactionList from "./TransactionList"
import type { Miner, Transaction } from "./types"

interface MinerRowProps {
  miner: Miner
  isExpanded: boolean
  onToggle: (minerId: string) => void
  isActive: boolean
  transactions: Transaction[]
}

export default function MinerRow({
  miner,
  isExpanded,
  onToggle,
  isActive,
  transactions,
}: {
  miner: Miner
  isExpanded: boolean
  onToggle: (minerId: string) => void
  isActive: boolean
  transactions: Transaction[]
}) {
  return (
    <div className="border-b border-gray-800/80">
      <motion.div
        className={`grid grid-cols-3 p-4 cursor-pointer transition-colors duration-300 relative overflow-hidden ${
          isActive ? "bg-blue-900/30" : ""
        }`}
        onClick={() => onToggle(miner.id)}
        whileHover={{
          backgroundColor: "rgba(30, 58, 138, 0.2)",
          transition: { duration: 0.2 },
        }}
        whileTap={{ scale: 0.98 }}
      >
        {/* Ripple effect on click */}
        {isActive && (
          <motion.div
            className="absolute inset-0 bg-blue-500/20 rounded-full"
            initial={{ scale: 0, x: "50%", y: "50%" }}
            animate={{ scale: 5, opacity: [2, 0] }}
            transition={{ duration: 2 }}
          />
        )}

        <div className="flex items-center  relative z-10">
          <motion.div
            animate={{ rotate: isExpanded ? 180 : 0 }}
            transition={{ duration: 0.4, type: "spring", stiffness: 200 }}
            className="mr-2"
          >
            <ChevronDown className="h-5 w-5  text-blue-400" />
          </motion.div>
          <motion.span
            className="text-blue-100 font-medium"
            animate={{
              color: isExpanded ? "#93c5fd" : "#e0e7ff",
            }}
            transition={{ duration: 0.3 }}
          >
            {miner.name}
          </motion.span>

          {/* Animated indicator */}
          {isExpanded && (
            <motion.div initial={{ opacity: 0, scale: 0 }} animate={{ opacity: 1, scale: 1 }} className="ml-2">
              <Zap className="h-4 w-4 text-yellow-400" />
            </motion.div>
          )}
        </div>
        <div className="text-gray-300 relative z-10">{miner.timestamp}</div>
        <div className="text-purple-300 font-medium relative z-10">
          <motion.div animate={{ scale: isActive ? [1, 1.2, 1] : 1 }} transition={{ duration: 0.4 }}>
            {miner.transactions}
          </motion.div>
        </div>
      </motion.div>

      <AnimatePresence>
        {isExpanded && (
          <motion.div
            initial={{ height: 0, opacity: 0 }}
            animate={{ height: "auto", opacity: 1 }}
            exit={{ height: 0, opacity: 0 }}
            transition={{ duration: 0.5, type: "spring", stiffness: 100, damping: 15 }}
            className="overflow-hidden"
          >
            <TransactionList transactions={transactions} />
          </motion.div>
        )}
      </AnimatePresence>
    </div>
  )
}