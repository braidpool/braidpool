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
    <div className="pl-2 sm:pl-10 pr-2 sm:pr-4 pb-3 bg-gradient-to-b from-blue-900/20 to-transparent">
      <motion.div
        className="text-blue-400 mb-3 font-medium flex items-center"
        initial={{ x: -20, opacity: 0 }}
        animate={{ x: 0, opacity: 1 }}
        transition={{ delay: 0.1 }}
      >
        <Activity className="h-4 w-4 mr-2" />
        Included {transactions.length} Transactions
      </motion.div>

      {/* Table header for desktop only */}
      <div className="hidden sm:grid grid-cols-6 text-xs text-blue-300 font-semibold mb-2 px-2">
        <div>Hash</div>
        <div>Size (vbytes)</div>
        <div>Fee (BTC)</div>
        <div>Fee Rate (sats/vB)</div>
        <div>Inputs</div>
        <div>Outputs</div>
      </div>

      <motion.div
        variants={{
          hidden: { opacity: 0 },
          show: { opacity: 1, transition: { staggerChildren: 0.1 } },
        }}
        initial="hidden"
        animate="show"
        className="w-full"
      >
        {transactions.map((transaction, index) => (
          <motion.div
            key={transaction.id}
            variants={{
              hidden: { y: 20, opacity: 0 },
              show: { y: 0, opacity: 1 },
            }}
            // Card for mobile, grid for desktop
            className="rounded-lg transition-all duration-300 group relative bg-blue-950/30 sm:bg-transparent
              sm:grid sm:grid-cols-6 sm:py-2.5 sm:px-0 px-3 py-3 flex flex-col gap-1"
            whileHover={{
              scale: 1.01,
              backgroundColor: 'rgba(30, 58, 138, 0.2)',
            }}
            onMouseEnter={() => setHoveredTransaction(transaction.id)}
            onMouseLeave={() => setHoveredTransaction(null)}
          >
            {/* Desktop grid cells */}
            <div className="hidden sm:block text-cyan-400 font-mono truncate relative z-10 group-hover:text-cyan-300 transition-colors duration-300">
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
            <div className="hidden sm:block text-gray-400 truncate relative z-10 group-hover:text-gray-300 transition-colors duration-300">
              {transaction.size} vbytes
            </div>
            <div className="hidden sm:block text-emerald-300 truncate relative z-10 group-hover:text-emerald-200 transition-colors duration-300">
              {transaction.fee ?? transaction.feePaid} BTC
            </div>
            <div className="hidden sm:block text-amber-300 truncate relative z-10 group-hover:text-amber-200 transition-colors duration-300">
              {transaction.feeRate} sats/vB
            </div>
            <div className="hidden sm:block text-purple-300 truncate relative z-10 group-hover:text-purple-200 transition-colors duration-300">
              {transaction.inputs} in
            </div>
            <div className="hidden sm:block text-blue-300 truncate relative z-10 group-hover:text-blue-200 transition-colors duration-300">
              {transaction.outputs} out
            </div>

            {/* Mobile card layout */}
            <div className="flex flex-col gap-1 sm:hidden">
              <div>
                <span className="font-semibold text-blue-300">Hash: </span>
                <span className="text-cyan-400 font-mono">
                  {shortenHash(transaction.hash)}
                </span>
              </div>
              <div>
                <span className="font-semibold text-blue-300">Size: </span>
                <span className="text-gray-400">{transaction.size} vbytes</span>
              </div>
              <div>
                <span className="font-semibold text-blue-300">Fee: </span>
                <span className="text-emerald-300">
                  {transaction.fee ?? transaction.feePaid} BTC
                </span>
              </div>
              <div>
                <span className="font-semibold text-blue-300">Fee Rate: </span>
                <span className="text-amber-300">
                  {transaction.feeRate} sats/vB
                </span>
              </div>
              <div>
                <span className="font-semibold text-blue-300">Inputs: </span>
                <span className="text-purple-300">{transaction.inputs} in</span>
              </div>
              <div>
                <span className="font-semibold text-blue-300">Outputs: </span>
                <span className="text-blue-300">{transaction.outputs} out</span>
              </div>
            </div>
          </motion.div>
        ))}
      </motion.div>
    </div>
  );
}
