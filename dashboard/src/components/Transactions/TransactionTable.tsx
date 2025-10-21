import React, { useState, useEffect, useRef } from "react";
import Card from "../common/Card";
import {
  TransactionCategory,
  TRANSACTION_CATEGORY_LABELS,
  TransactionTableProps,
} from "./type";
import {
  truncateHash,
  formatFee,
  formatFeeRate,
  formatTime,
  getCategoryColor,
} from "./utils";

const TransactionTable: React.FC<TransactionTableProps> = ({
  transactions = [],
  loading = false,
  error = null,
  maxHeight = 600,
  autoRefresh = false,
  refreshInterval = 30000,
}) => {
  const [categoryFilter, setCategoryFilter] = useState<TransactionCategory[]>(
    [],
  );
  const [isFilterOpen, setIsFilterOpen] = useState(false);
  const dropdownRef = useRef<HTMLDivElement>(null);

  // Close dropdown
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
      document.addEventListener("mousedown", handleClickOutside);
      return () =>
        document.removeEventListener("mousedown", handleClickOutside);
    }
  }, [isFilterOpen]);

  const handleCategoryToggle = (category: TransactionCategory) => {
    setCategoryFilter((prev) =>
      prev.includes(category)
        ? prev.filter((c) => c !== category)
        : [...prev, category],
    );
  };

  const filteredTransactions = transactions.filter((tx) => {
    if (categoryFilter.length === 0) return true;
    if (!tx.category) return false;
    return categoryFilter.includes(tx.category as TransactionCategory);
  });

  return (
    <div className="space-y-4">
      {/* Filters - OUTSIDE Card to avoid overflow issues */}
      <div className="flex items-center justify-between px-4">
        <div className="relative" ref={dropdownRef}>
          <button
            onClick={() => setIsFilterOpen(!isFilterOpen)}
            className="px-4 py-2 bg-gray-800 border border-gray-700 rounded-lg text-sm text-gray-300 hover:bg-gray-750 focus:outline-none focus:ring-2 focus:ring-blue-500 transition-colors"
          >
            {categoryFilter.length === 0
              ? "Filter by category"
              : `${categoryFilter.length} selected`}
          </button>

          {isFilterOpen && (
            <div className="absolute left-0 mt-2 w-64 bg-gray-800 border border-gray-700 rounded-lg shadow-xl z-50">
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

        {categoryFilter.length > 0 && (
          <button
            onClick={() => setCategoryFilter([])}
            className="text-sm text-gray-400 hover:text-white transition-colors"
          >
            Clear filters
          </button>
        )}
      </div>

      {/* Error */}
      {error && (
        <div className="px-4">
          <div className="p-4 bg-red-500/10 border border-red-500/20 rounded-lg">
            <p className="text-sm text-red-400">{error}</p>
          </div>
        </div>
      )}

      {/* Table Card */}
      <Card
        title="Transaction Table"
        subtitle={`${filteredTransactions.length} of ${transactions.length} transactions`}
        accentColor="#1976d2"
      >
        <div
          className="overflow-auto rounded-lg border border-gray-800"
          style={{ maxHeight: `${maxHeight}px` }}
        >
          <table className="w-full text-sm">
            <thead className="sticky top-0 bg-gray-900 z-10">
              <tr className="border-b border-gray-800">
                <th className="px-4 py-3 text-left font-semibold text-gray-300 text-xs uppercase">
                  Hash
                </th>
                <th className="px-4 py-3 text-left font-semibold text-gray-300 text-xs uppercase">
                  Category
                </th>
                <th className="px-4 py-3 text-right font-semibold text-gray-300 text-xs uppercase">
                  Size
                </th>
                <th className="px-4 py-3 text-right font-semibold text-gray-300 text-xs uppercase">
                  Fee
                </th>
                <th className="px-4 py-3 text-right font-semibold text-gray-300 text-xs uppercase">
                  Fee Rate
                </th>
                <th className="px-4 py-3 text-center font-semibold text-gray-300 text-xs uppercase">
                  I/O
                </th>
                <th className="px-4 py-3 text-center font-semibold text-gray-300 text-xs uppercase">
                  Status
                </th>
                <th className="px-4 py-3 text-right font-semibold text-gray-300 text-xs uppercase">
                  Time
                </th>
              </tr>
            </thead>
            <tbody className="divide-y divide-gray-800">
              {loading ? (
                <tr>
                  <td colSpan={8} className="py-12 text-center">
                    <div className="flex justify-center">
                      <div className="w-8 h-8 border-2 border-blue-500 border-t-transparent rounded-full animate-spin"></div>
                    </div>
                  </td>
                </tr>
              ) : filteredTransactions.length === 0 ? (
                <tr>
                  <td colSpan={8} className="py-12 text-center text-gray-500">
                    No transactions found
                  </td>
                </tr>
              ) : (
                filteredTransactions.map((tx) => (
                  <tr
                    key={tx.txid}
                    className="hover:bg-gray-800/50 transition-colors"
                  >
                    <td className="px-4 py-3 font-mono text-blue-400">
                      {truncateHash(tx.txid)}
                    </td>
                    <td className="px-4 py-3">
                      <span
                        className={`inline-block px-2 py-1 rounded text-xs font-medium ${tx.category
                          ? getCategoryColor(tx.category)
                          : "bg-gray-500/10 text-gray-400"
                          }`}
                      >
                        {tx.category
                          ? TRANSACTION_CATEGORY_LABELS[tx.category]
                          : "Unknown"}
                      </span>
                    </td>
                    <td className="px-4 py-3 text-right font-mono text-white">
                      {tx.size ? tx.size.toLocaleString() : "-"}
                      <span className="text-xs text-gray-500 ml-1">vB</span>
                    </td>
                    <td className="px-4 py-3 text-right font-mono text-orange-400">
                      {tx.fee ? formatFee(tx.fee) : "-"}
                    </td>
                    <td className="px-4 py-3 text-right font-mono text-yellow-400">
                      {tx.feeRate ? formatFeeRate(tx.feeRate) : "-"}
                    </td>
                    <td className="px-4 py-3 text-center text-white">
                      <span className="text-blue-400">{tx.inputs || "?"}</span>
                      <span className="text-gray-600 mx-1">/</span>
                      <span className="text-green-400">
                        {tx.outputs || "?"}
                      </span>
                    </td>
                    <td className="px-4 py-3 text-center">
                      {tx.confirmations ? (
                        <span
                          className={`inline-block px-2 py-1 rounded text-xs font-medium border ${tx.confirmations >= 6
                            ? "border-green-500/30 bg-green-500/10 text-green-400"
                            : "border-yellow-500/30 bg-yellow-500/10 text-yellow-400"
                            }`}
                        >
                          {tx.confirmations}
                        </span>
                      ) : (
                        <span className="text-sm text-gray-500">Pending</span>
                      )}
                    </td>
                    <td className="px-4 py-3 text-right text-gray-400">
                      {formatTime(tx.timestamp)}
                    </td>
                  </tr>
                ))
              )}
            </tbody>
          </table>
        </div>

        {/* Footer */}
        {!loading && filteredTransactions.length > 0 && (
          <div className="mt-4 pt-4 border-t border-gray-800 flex items-center justify-between text-sm text-gray-400">
            <span>
              Showing {filteredTransactions.length} of {transactions.length}{" "}
              transactions
            </span>
            {autoRefresh && (
              <span className="flex items-center gap-2">
                <span className="w-2 h-2 bg-green-500 rounded-full animate-pulse"></span>
                Auto-refresh every {refreshInterval / 1000}s
              </span>
            )}
          </div>
        )}
      </Card>
    </div>
  );
};

export default TransactionTable;
