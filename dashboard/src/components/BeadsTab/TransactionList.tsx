import { shortenHash } from './lib/Utils';
import { TransactionListProps } from './lib/Types';
import { Activity } from 'lucide-react';
import useCopyToClipboard from './lib/Utils';
export default function TransactionList({
  transactions,
}: TransactionListProps) {
  const limitedTransactions = transactions.slice(0, 10);
  const hasMoreTransactions = transactions.length > 10;
  const { copied, copy } = useCopyToClipboard();

  return (
    <div className="pl-4 sm:pl-10 pr-4 pb-3 ">
      <div className="text-white mb-3 font-medium flex items-center text-sm">
        <Activity className="h-4 w-4 mr-2 flex-shrink-0" />
        Showing {limitedTransactions.length} of {transactions.length}{' '}
        Transactions
        {hasMoreTransactions && (
          <span className="text-gray-400 text-xs ml-2">
            (displaying first 10)
          </span>
        )}
      </div>

      <div className="overflow-x-auto">
        <div className="min-w-[700px]">
          {/* Table header */}
          <div className="grid  grid-cols-6 text-sm text-blue-300 font-semibold ml-4 mb-2 px-2">
            <div>Hash</div>
            <div>Size</div>
            <div>Fee</div>
            <div>Fee Rate</div>
            <div>Inputs</div>
            <div>Outputs</div>
          </div>

          {/* Transaction rows */}
          {limitedTransactions.map((transaction) => (
            <div
              key={transaction.id}
              className="grid grid-cols-6 gap-2 py-2.5 px-2 rounded-lg transition-all duration-300  group relative text-sm sm:text-sm"
            >
              <div className="flex flex-wrap gap-2">
                <div className="relative">
                  <button
                    className="text-white font-mono text-xs sm:text-sm hover:text-cyan-300 hover:underline truncate max-w-[150px] sm:max-w-[200px]"
                    onClick={(e) => {
                      e.stopPropagation();
                      copy(transaction.hash);
                    }}
                  >
                    {shortenHash(transaction.hash)}
                  </button>
                  {copied === transaction.hash && (
                    <span className="px-2 text-green-400 text-xs">Copied!</span>
                  )}
                </div>
              </div>

              <div className="text-white text-sm relative z-10  group-hover:text-gray-300 transition-colors duration-300">
                {transaction.size} vB
              </div>
              <div className="text-white text-sm relative z-10  group-hover:text-gray-300 transition-colors duration-300">
                {transaction.fee.toFixed(8)} BTC
              </div>
              <div className="text-white text-sm relative z-10 group-hover:text-gray-300 transition-colors duration-300">
                {transaction.feeRate.toFixed(2)} sats/vB
              </div>
              <div className="text-white text-sm relative z-10  group-hover:text-gray-300 transition-colors duration-300">
                {transaction.inputs}
              </div>
              <div className="text-white text-sm relative z-10  group-hover:text-gray-300 transition-colors duration-300">
                {transaction.outputs}
              </div>
            </div>
          ))}
        </div>
      </div>
    </div>
  );
}
