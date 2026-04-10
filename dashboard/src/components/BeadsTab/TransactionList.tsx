import { shortenHash, useCopyToClipboard } from './lib/Utils';
import { TransactionListProps } from './lib/Types';
import { Activity } from 'lucide-react';
export default function TransactionList({
  transactions,
}: TransactionListProps) {
  const limitedTransactions = transactions.slice(0, 10);
  const hasMoreTransactions = transactions.length > 10;
  const { copied, copy } = useCopyToClipboard();

  return (
    <div className="pl-4 sm:pl-10 pr-4 pb-3">
      <div className="text-textPrimary mb-3 font-medium flex items-center text-sm">
        <Activity className="h-4 w-4 mr-2 flex-shrink-0" />
        Showing {limitedTransactions.length} of {transactions.length}{' '}
        Transactions
        {hasMoreTransactions && (
          <span className="text-textSecondary text-xs ml-2">
            (displaying first 10)
          </span>
        )}
      </div>

      {/* Table view for large screens */}
      <div className="overflow-x-auto sm:hidden max-md:hidden lg:block">
        <div className="min-w-[700px]">
          {/* Table header */}
          <div className="grid grid-cols-6 text-sm text-blue-300 font-semibold ml-4 mb-2 px-2">
            <div>Hash</div>
            <div>Size</div>
            <div>Fee</div>
            <div>Fee Rate</div>
            <div>Inputs</div>
            <div>Outputs</div>
          </div>

          {/* Table Rows */}
          {limitedTransactions.map((transaction) => (
            <div
              key={transaction.id}
              className="grid grid-cols-6 gap-2 py-2.5 px-2 rounded-lg transition-all duration-300 group relative text-sm"
            >
              <div className="flex flex-wrap gap-2">
                <div className="relative">
                  <button
                    className="text-textPrimary font-mono text-xs hover:text-cyan-300 hover:underline truncate max-w-[200px]"
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
              <div className="text-textPrimary group-hover:text-textSecondary">
                {transaction.size} vB
              </div>
              <div className="text-textPrimary group-hover:text-textSecondary">
                {transaction.fee.toFixed(8)} BTC
              </div>
              <div className="text-textPrimary group-hover:text-textSecondary">
                {transaction.feeRate.toFixed(2)} sats/vB
              </div>
              <div className="text-textPrimary group-hover:text-textSecondary">
                {transaction.inputs}
              </div>
              <div className="text-textPrimary group-hover:text-textSecondary">
                {transaction.outputs}
              </div>
            </div>
          ))}
        </div>
      </div>

      {/* Mobile / Tablet card view */}
      <div className="sm:block lg:hidden px-2 sm:px-4">
        <div className="space-y-3 sm:space-y-4">
          {limitedTransactions.map((transaction) => (
            <div
              key={transaction.id}
              className="border border-border rounded-lg p-3 sm:p-4 space-y-2"
            >
              {/* Stats */}
              <div className="grid grid-cols-2 gap-2 text-xs sm:text-sm">
                <div>
                  <span className="text-textSecondary">Hash:</span>
                  <div className="text-textPrimary font-medium">
                    <div className="relative">
                      <button
                        className="text-textPrimary font-mono text-xs hover:text-cyan-300 hover:underline truncate max-w-[200px]"
                        onClick={(e) => {
                          e.stopPropagation();
                          copy(transaction.hash);
                        }}
                      >
                        {shortenHash(transaction.hash)}
                      </button>
                      {copied === transaction.hash && (
                        <span className="px-2 text-green-400 text-xs">
                          Copied!
                        </span>
                      )}
                    </div>
                  </div>
                </div>
                <div>
                  <span className="text-textSecondary">Size:</span>
                  <div className="text-textPrimary font-medium">
                    {transaction.size}vB
                  </div>
                </div>
                <div>
                  <span className="text-textSecondary">Fee:</span>
                  <div className="text-textPrimary font-medium">
                    {transaction.fee} BTC
                  </div>
                </div>
                <div>
                  <span className="text-textSecondary">Fee Rate:</span>
                  <div className="text-textPrimary font-medium">
                    {transaction.feeRate} sats/vB
                  </div>
                </div>
                <div>
                  <span className="text-textSecondary">Inputs:</span>
                  <div className="text-textPrimary font-medium">
                    {transaction.inputs}
                  </div>
                </div>
                <div>
                  <span className="text-textSecondary">Outputs:</span>
                  <div className="text-textPrimary font-medium">
                    {transaction.outputs}
                  </div>
                </div>
              </div>
            </div>
          ))}
        </div>
      </div>
    </div>
  );
}
