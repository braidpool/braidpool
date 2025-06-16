import { useState } from 'react';
import { Activity } from 'lucide-react';
import { shortenHash } from './lib/utils/utils';
import { TransactionListProps } from './lib/types';
export default function TransactionList({
  transactions,
}: TransactionListProps) {
  const [hoveredTransaction, setHoveredTransaction] = useState<string | null>(
    null
  );

  return (
    <div className="pl-4 sm:pl-10 pr-4 pb-3 overflow-x-auto">
      <div className="text-white mb-3 font-medium flex items-center text-sm sm:text-base">
        <Activity className="h-4 w-4 mr-2 flex-shrink-0" />
        Included {transactions.length} Transactions
      </div>

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
      <div className="min-w-[640px] sm:min-w-0">
        {transactions.map((transaction, index) => (
          <div className="grid grid-cols-6 gap-2  py-2.5 rounded-lg transition-all duration-300 group relative text-xs sm:text-sm">
            {/* Hover glow effect */}
            <div className="absolute inset-0 bg-slate-600 opacity-0 group-hover:opacity-100 rounded-lg transition-opacity duration-300"></div>

            <div className="text-white font-mono relative z-10 group-hover:text-cyan-300 transition-colors duration-300 truncate">
              <span>{shortenHash(transaction.hash)}</span>
              {/* Tooltip on hover */}
              {hoveredTransaction === transaction.id && (
                <div className="absolute left-0 -top-10 bg-gray-900/90 border border-blue-500/30 rounded-md p-2 text-xs text-white z-20">
                  Transaction hash for block #{transaction.blockId}
                </div>
              )}
            </div>
            <div className="text-white relative z-10 group-hover:text-gray-300 transition-colors duration-300">
              {transaction.size} vbytes
            </div>
            <div className="text-white relative z-10 group-hover:text-emerald-200 transition-colors duration-300">
              {transaction.fee !== undefined
                ? transaction.fee
                : transaction.feePaid}{' '}
              BTC
            </div>
            <div className="text-white relative z-10 group-hover:text-amber-200 transition-colors duration-300">
              {transaction.feeRate} sats/vB
            </div>
            <div className="text-white relative z-10 group-hover:text-purple-200 transition-colors duration-300">
              {transaction.inputs} in
            </div>
            <div className="text-white relative z-10 group-hover:text-blue-200 transition-colors duration-300">
              {transaction.outputs} out
            </div>
          </div>
        ))}
      </div>
    </div>
  );
}
