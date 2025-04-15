

import { useState } from "react"
import { motion} from "framer-motion"
import {
  
  Activity,
  
} from "lucide-react"
import type { Transaction } from "./types"


interface TransactionListProps {
  transactions: Transaction[]
}

export default function TransactionList({ transactions }: { transactions: Transaction[] }) {
  const [hoveredTransaction, setHoveredTransaction] = useState<string | null>(null)

  return (
    <div className="pl-10 pr-4 pb-3 bg-gradient-to-b from-blue-900/20 to-transparent">
      <motion.div
        className="text-blue-400 mb-3 font-medium flex items-center"
        initial={{ x: -20, opacity: 0 }}
        animate={{ x: 0, opacity: 1 }}
        transition={{ delay: 0.1 }}
      >
        <Activity className="h-4 w-4 mr-2" />
        Included {transactions.length} Transactions
      </motion.div>

      {/* Transaction rows with staggered animation */}
      <motion.div
        variants={{
          hidden: { opacity: 0 },
          show: {
            opacity: 1,
            transition: {
              staggerChildren: 0.1,
            },
          },
        }}
        initial="hidden"
        animate="show"
      >
        {transactions.map((transaction, index) => (
          <motion.div
            key={transaction.id}
            variants={{
              hidden: { y: 20, opacity: 0 },
              show: { y: 0, opacity: 1 },
            }}
            className="grid grid-cols-3 py-2.5 rounded-lg transition-all duration-300 group relative"
            whileHover={{ scale: 1.01, backgroundColor: "rgba(30, 58, 138, 0.2)" }}
            onMouseEnter={() => setHoveredTransaction(transaction.id)}
            onMouseLeave={() => setHoveredTransaction(null)}
          >
            {/* Hover glow effect */}
            <div className="absolute inset-0 bg-blue-500/5 opacity-0 group-hover:opacity-100 rounded-lg transition-opacity duration-300"></div>

            <div className="text-cyan-400 font-mono relative z-10 group-hover:text-cyan-300 transition-colors duration-300">
              <motion.span
                animate={{ opacity: [0.7, 1, 0.7] }}
                transition={{ duration: 3, repeat: Number.POSITIVE_INFINITY, delay: index * 0.5 }}
              >
                {transaction.hash}
              </motion.span>
            </div>
            <div className="text-gray-400 relative z-10 group-hover:text-gray-300 transition-colors duration-300">
              {transaction.timestamp}
            </div>
            <div className="text-purple-300 font-medium relative z-10 group-hover:text-purple-200 transition-colors duration-300">
              <motion.span whileHover={{ scale: 1.2 }} transition={{ type: "spring", stiffness: 400 }}>
                {transaction.count}
              </motion.span>
            </div>

            {/* Tooltip on hover */}
            {hoveredTransaction === transaction.id && (
              <motion.div
                className="absolute left-0 -top-10 bg-gray-900/90 border border-blue-500/30 rounded-md p-2 text-xs text-white z-20"
                initial={{ opacity: 0, y: 5 }}
                animate={{ opacity: 1, y: 0 }}
                exit={{ opacity: 0, y: 5 }}
              >
                Transaction hash for block #{transaction.blockId}
              </motion.div>
            )}
          </motion.div>
        ))}
      </motion.div>
    </div>
  )
}