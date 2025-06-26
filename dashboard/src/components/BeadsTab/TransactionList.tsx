import { useState } from 'react';
import { motion } from 'framer-motion';
import { Activity } from 'lucide-react';
import type { Transaction } from './lib/types';

import { shortenHash } from './lib/utils/shortenHash';

interface TransactionListProps {
  transactions: Transaction[];
}

export default function TransactionList({
  transactions,
}: TransactionListProps) {
  const [hoveredTransaction, setHoveredTransaction] = useState<string | null>(
    null
  );

  return (
    // Updated - Added responsive padding and overflow handling
    <div className="pl-4 sm:pl-10 pr-4 pb-3 bg-gradient-to-b from-blue-900/20 to-transparent overflow-x-auto">
      <motion.div
        className="text-blue-400 mb-3 font-medium flex items-center text-sm sm:text-base"
        initial={{ x: -20, opacity: 0 }}
        animate={{ x: 0, opacity: 1 }}
        transition={{ delay: 0.1 }}
      >
        <Activity className="h-4 w-4 mr-2 flex-shrink-0" />
        Included {transactions.length} Transactions
      </motion.div>

      {/* Table header for transaction details */}
      <div className="grid sm:grid grid-cols-6 text-xs text-blue-300 font-semibold mb-2 px-2">
        <div>Hash</div>
        <div>Size (vbytes)</div>
        <div>Fee (BTC)</div>
        <div>Fee Rate (sats/vB)</div>
        <div>Inputs</div>
        <div>Outputs</div>
      </div>

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
        className="min-w-[640px] sm:min-w-0"
      >
        {transactions.map((transaction, index) => (
          <motion.div
            key={transaction.id}
            variants={{
              hidden: { y: 20, opacity: 0 },
              show: { y: 0, opacity: 1 },
            }}
            className="grid grid-cols-6 gap-2 py-2.5 rounded-lg transition-all duration-300 group relative text-xs sm:text-sm"
            whileHover={{
              scale: 1.01,
              backgroundColor: 'rgba(30, 58, 138, 0.2)',
            }}
            onMouseEnter={() => setHoveredTransaction(transaction.id)}
            onMouseLeave={() => setHoveredTransaction(null)}
          >
            {/* Hover glow effect */}
            <div className="absolute inset-0 bg-blue-500/5 opacity-0 group-hover:opacity-100 rounded-lg transition-opacity duration-300"></div>

            <div className="text-cyan-400 font-mono relative z-10 group-hover:text-cyan-300 transition-colors duration-300 truncate">
              <motion.span
                animate={{ opacity: [0.7, 1, 0.7] }}
                transition={{
                  duration: 3,
                  repeat: Number.POSITIVE_INFINITY,
                  delay: index * 0.5,
                }}
              >
                {shortenHash(transaction.hash)}
              </motion.span>
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
            </div>
            <div className="text-gray-400 relative z-10 group-hover:text-gray-300 transition-colors duration-300">
              {transaction.size} vbytes
            </div>
            <div className="text-emerald-300 relative z-10 group-hover:text-emerald-200 transition-colors duration-300">
              {transaction.fee !== undefined
                ? transaction.fee
                : transaction.feePaid}{' '}
              BTC
            </div>
            <div className="text-amber-300 relative z-10 group-hover:text-amber-200 transition-colors duration-300">
              {transaction.feeRate} sats/vB
            </div>
            <div className="text-purple-300 relative z-10 group-hover:text-purple-200 transition-colors duration-300">
              {transaction.inputs} in
            </div>
            <div className="text-blue-300 relative z-10 group-hover:text-blue-200 transition-colors duration-300">
              {transaction.outputs} out
            </div>
          </motion.div>
        ))}
      </motion.div>
    </div>
  );
}
