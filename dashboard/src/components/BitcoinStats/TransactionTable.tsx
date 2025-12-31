import React, { useState, useRef, useEffect } from 'react';
import TransactionDialog from './TransactionDialog';
import { shortenAddress } from './Utils';
import colors from '../../theme/colors';
import { TransactionTableProps, TransactionCategory, TRANSACTION_CATEGORY_LABELS } from './Types';
import {
  formatFee,
  formatFeeRate,
  formatTime,
  getCategoryColor,
} from './Utils';

const TransactionTable: React.FC<TransactionTableProps> = ({
  transactions,
}) => {
  const [selectedTx, setSelectedTx] = useState<string | null>(null);
  const [categoryFilter, setCategoryFilter] = useState<TransactionCategory[]>([]);
  const [isFilterOpen, setIsFilterOpen] = useState(false);
  const dropdownRef = useRef<HTMLDivElement>(null);

  // Close dropdown when clicking outside
  useEffect(() => {
    const handleClickOutside = (event: MouseEvent) => {
      if (
        dropdownRef.current &&
        !dropdownRef.current.contains(event.target as Node)
      ) {
        setIsFilterOpen(false);
      }
    };

    if (isFilterOpen) {
      document.addEventListener('mousedown', handleClickOutside);
      return () => document.removeEventListener('mousedown', handleClickOutside);
    }
  }, [isFilterOpen]);

  const handleCategoryToggle = (category: TransactionCategory) => {
    setCategoryFilter((prev) =>
      prev.includes(category)
        ? prev.filter((c) => c !== category)
        : [...prev, category]
    );
  };

  // Filter transactions by category
  const filteredTransactions = transactions.filter((tx) => {
    if (categoryFilter.length === 0) return true;
    if (!tx.category) return false;
    return categoryFilter.includes(tx.category as TransactionCategory);
  });

  return (
    <div
      className="rounded-2xl border border-white/10 bg-[#1e1e1e] shadow-md p-4 mt-10"
      style={{ borderColor: colors.cardAccentSecondary }}
    >
      {/* Header with Filter */}
      <div className="mb-4 flex items-center justify-between">
        <div>
          <div className="text-gray-400">Latest Transactions</div>
          <div className="text-xs text-gray-500 mt-1">
            {filteredTransactions.length} of {transactions.length} transactions
          </div>
        </div>

        {/* Category Filter Dropdown */}
        <div className="flex items-center gap-4">
          {categoryFilter.length > 0 && (
            <button
              onClick={() => setCategoryFilter([])}
              className="text-sm text-gray-400 hover:text-white transition-colors"
            >
              Clear filters
            </button>
          )}

          <div className="relative" ref={dropdownRef}>
            <button
              onClick={() => setIsFilterOpen(!isFilterOpen)}
              className="px-4 py-2 bg-gray-800 border border-gray-700 rounded-lg text-sm text-gray-300 hover:bg-gray-750 focus:outline-none focus:ring-2 focus:ring-blue-500 transition-colors"
            >
              {categoryFilter.length === 0
                ? 'Filter by category'
                : `${categoryFilter.length} selected`}
            </button>

            {isFilterOpen && (
              <div className="absolute right-0 mt-2 w-64 bg-gray-800 border border-gray-700 rounded-lg shadow-xl z-50">
                <div className="p-2 max-h-80 overflow-auto">
                  {Object.values(TransactionCategory).map((category) => (
                    <label
                      key={category}
                      className="flex items-center gap-2 px-3 py-2 hover:bg-gray-700 rounded cursor-pointer transition-colors"
                    >
                      <input
                        type="checkbox"
                        checked={categoryFilter.includes(category)}
                        onChange={() => handleCategoryToggle(category)}
                        className="w-4 h-4 rounded border-gray-600 text-blue-600 focus:ring-blue-500"
                      />
                      <span
                        className={`px-2 py-0.5 rounded text-xs font-medium ${getCategoryColor(category)}`}
                      >
                        {TRANSACTION_CATEGORY_LABELS[category]}
                      </span>
                    </label>
                  ))}
                </div>
                <div className="p-2 border-t border-gray-700">
                  <button
                    onClick={() => {
                      setCategoryFilter([]);
                      setIsFilterOpen(false);
                    }}
                    className="w-full px-3 py-2 text-sm text-gray-400 hover:text-white hover:bg-gray-700 rounded transition-colors"
                  >
                    Clear all
                  </button>
                </div>
              </div>
            )}
          </div>
        </div>
      </div>

      {/* Table */}
      <div
        className="overflow-auto rounded-md scrollbar-thin"
        style={{
          maxHeight: '600px',
          scrollbarColor: `${colors.primary} ${colors.paper}`,
          backgroundColor: colors.paper,
        }}
      >
        <table className="w-full">
          {transactions.length === 0 ? null : (
            <thead className="sticky top-0 z-10" style={{ backgroundColor: colors.paper }}>
              <tr>
                <th
                  className="text-left px-4 py-3 font-semibold text-xs uppercase"
                  style={{ color: colors.textPrimary }}
                >
                  TXID
                </th>
                <th
                  className="text-left px-4 py-3 font-semibold text-xs uppercase"
                  style={{ color: colors.textPrimary }}
                >
                  CATEGORY
                </th>
                <th
                  className="text-right px-4 py-3 font-semibold text-xs uppercase"
                  style={{ color: colors.textPrimary }}
                >
                  FEE
                </th>
                <th
                  className="text-right px-4 py-3 font-semibold text-xs uppercase"
                  style={{ color: colors.textPrimary }}
                >
                  FEE RATE
                </th>
                <th
                  className="text-right px-4 py-3 font-semibold text-xs uppercase"
                  style={{ color: colors.textPrimary }}
                >
                  SIZE
                </th>
                <th
                  className="text-center px-4 py-3 font-semibold text-xs uppercase"
                  style={{ color: colors.textPrimary }}
                >
                  I/O
                </th>
                <th
                  className="text-center px-4 py-3 font-semibold text-xs uppercase"
                  style={{ color: colors.textPrimary }}
                >
                  STATUS
                </th>
                <th
                  className="text-right px-4 py-3 font-semibold text-xs uppercase"
                  style={{ color: colors.textPrimary }}
                >
                  TIME
                </th>
              </tr>
            </thead>
          )}
          <tbody>
            {transactions.length === 0 ? (
              <tr>
                <td
                  colSpan={8}
                  className="p-4 text-center text-sm text-gray-400"
                >
                  No transactions found
                </td>
              </tr>
            ) : filteredTransactions.length === 0 ? (
              <tr>
                <td
                  colSpan={8}
                  className="p-4 text-center text-sm text-gray-400"
                >
                  No transactions match the selected filters
                </td>
              </tr>
            ) : (
              filteredTransactions.map((tx) => (
                <tr
                  key={tx.txid}
                  className="transition-colors duration-150 hover:bg-white/5 cursor-pointer"
                  onClick={() => setSelectedTx(tx.txid)}
                >
                  <td className="px-4 py-3">
                    <div className="relative group inline-block">
                      <span
                        className="cursor-pointer hover:underline font-mono"
                        style={{ color: colors.accent }}
                      >
                        {shortenAddress(tx.txid)}
                      </span>
                      <div
                        className="absolute z-50 opacity-0 group-hover:opacity-100 transition-opacity duration-200 
                          bg-gray-800 text-white p-2 rounded shadow-lg text-xs whitespace-nowrap
                          left-full top-1/2 -translate-y-1/2 ml-2"
                      >
                        {tx.txid}
                      </div>
                    </div>
                  </td>
                  <td className="px-4 py-3">
                    {tx.category ? (
                      <span
                        className={`inline-block px-2 py-1 rounded text-xs font-medium ${getCategoryColor(tx.category)}`}
                      >
                        {TRANSACTION_CATEGORY_LABELS[tx.category]}
                      </span>
                    ) : (
                      <span className="text-xs text-gray-500">-</span>
                    )}
                  </td>
                  <td className="px-4 py-3 text-right font-mono" style={{ color: colors.textPrimary }}>
                    {tx.fee ? formatFee(tx.fee) : '-'}
                    {tx.fee && <span className="text-xs text-gray-500 ml-1">BTC</span>}
                  </td>
                  <td className="px-4 py-3 text-right font-mono text-yellow-400">
                    {tx.feeRate ? formatFeeRate(tx.feeRate) : '-'}
                    {tx.feeRate && <span className="text-xs text-gray-500 ml-1">sat/vB</span>}
                  </td>
                  <td className="px-4 py-3 text-right font-mono" style={{ color: colors.textPrimary }}>
                    {tx.size || tx.size ? (
                      <>
                        {(tx.size || tx.size).toLocaleString()}
                        <span className="text-xs text-gray-500 ml-1">vB</span>
                      </>
                    ) : '-'}
                  </td>
                  <td className="px-4 py-3 text-center text-white">
                    {tx.inputs !== undefined && tx.outputs !== undefined ? (
                      <>
                        <span className="text-blue-400">{tx.inputs}</span>
                        <span className="text-gray-600 mx-1">/</span>
                        <span className="text-green-400">{tx.outputs}</span>
                      </>
                    ) : (
                      <span className="text-gray-500">-</span>
                    )}
                  </td>
                  <td className="px-4 py-3 text-center">
                    {tx.confirmations !== undefined && tx.confirmations > 0 ? (
                      <span
                        className={`inline-block px-2 py-1 rounded text-xs font-medium border ${tx.confirmations >= 6
                          ? 'border-green-500/30 bg-green-500/10 text-green-400'
                          : 'border-yellow-500/30 bg-yellow-500/10 text-yellow-400'
                          }`}
                      >
                        {tx.confirmations}
                      </span>
                    ) : (
                      <span className="text-sm text-gray-500">Pending</span>
                    )}
                  </td>
                  <td className="px-4 py-3 text-right text-gray-400">
                    {tx.timestamp ? formatTime(tx.timestamp) : '-'}
                  </td>
                </tr>
              ))
            )}
          </tbody>
        </table>

        {selectedTx && (
          <TransactionDialog
            txid={selectedTx}
            onClose={() => setSelectedTx(null)}
          />
        )}
      </div>

      {/* Footer */}
      {filteredTransactions.length > 0 && (
        <div className="mt-4 pt-4 border-t border-gray-800 flex items-center justify-between text-sm text-gray-400">
          <span>
            Showing {filteredTransactions.length} of {transactions.length} transactions
          </span>
          <span className="flex items-center gap-2">
            <span className="w-2 h-2 bg-green-500 rounded-full animate-pulse"></span>
            Auto-refresh every 30s
          </span>
        </div>
      )}
    </div>
  );
};

export default TransactionTable;