import React, { useState, useEffect, useCallback } from "react";
import { braidpoolApi } from "../../utils/braidpoolApi";
import TransactionTable from "./TransactionTable";
import {
  TRANSACTION_CATEGORY_LABELS,
  TRANSACTION_CATEGORY_DESCRIPTIONS,
  TransactionCategory,
  BraidPoolTransaction,
} from "./Types";
import { getCategoryStyles } from "./Utils";

const TransactionsPage: React.FC = () => {
  const [transactions, setTransactions] = useState<BraidPoolTransaction[]>([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [autoRefresh, setAutoRefresh] = useState(true);
  const [refreshInterval] = useState(30000);

  const fetchTransactions = useCallback(async () => {
    try {
      setLoading(true);
      setError(null);
      const data = await braidpoolApi.fetchRecentTransactions(50);
      setTransactions(data);
    } catch (err) {
      console.error("Failed to fetch transactions:", err);
      setError("Failed to load transactions. Please try again.");
    } finally {
      setLoading(false);
    }
  }, []);

  useEffect(() => {
    fetchTransactions();
  }, [fetchTransactions]);

  useEffect(() => {
    if (autoRefresh) {
      const interval = setInterval(fetchTransactions, refreshInterval);
      return () => clearInterval(interval);
    }
  }, [autoRefresh, fetchTransactions, refreshInterval]);

  const handleAutoRefreshChange = (
    event: React.ChangeEvent<HTMLInputElement>,
  ) => {
    setAutoRefresh(event.target.checked);
  };

  return (
    <div className="min-h-screen" style={{ backgroundColor: 'rgba(18, 18, 18, 1)' }}>
      <div className="max-w-7xl mx-auto px-4 sm:px-6 lg:px-8 py-8">
        {/* Header Card */}
        <div 
          className="relative px-6 py-6 rounded border border-black/5 mb-6 shadow-sm"
          style={{ backgroundColor: 'rgba(30, 30, 30, 1)' }}
        >
          <div className="absolute top-0 left-0 w-1 h-full" style={{ backgroundColor: '#1976d2' }} />
          <div className="px-3">
            <h1 className="text-3xl font-bold text-white mb-2">
              Transaction Management
            </h1>
            <p className="text-gray-400">
              Monitor and analyze Bitcoin transactions across different categories
              and states
            </p>
          </div>
        </div>

        {/* Categories Card */}
        <div 
          className="relative px-6 py-6 rounded border border-black/5 mb-6 shadow-sm"
          style={{ backgroundColor: 'rgba(30, 30, 30, 1)' }}
        >
          <div className="absolute top-0 left-0 w-1 h-full" style={{ backgroundColor: '#1976d2' }} />
          <div className="px-3">
            <h2 className="text-base font-medium text-white mb-4">
              Transaction Categories
            </h2>
            <div className="grid grid-cols-1 sm:grid-cols-2 lg:grid-cols-3 xl:grid-cols-6 gap-4">
              {Object.entries(TRANSACTION_CATEGORY_LABELS).map(([key, label]) => {
                const category = key as TransactionCategory;
                return (
                  <div
                    key={category}
                    className={`p-4 rounded-lg border ${getCategoryStyles(category)} hover:border-opacity-40 transition-colors`}
                    title={TRANSACTION_CATEGORY_DESCRIPTIONS[category]}
                  >
                    <div className="font-medium text-sm mb-1">{label}</div>
                    <p className="text-xs text-gray-500 line-clamp-2">
                      {TRANSACTION_CATEGORY_DESCRIPTIONS[category]}
                    </p>
                  </div>
                );
              })}
            </div>
          </div>
        </div>

        {/* Controls Card */}
        <div 
          className="relative px-6 py-4 rounded border border-black/5 mb-6 shadow-sm"
          style={{ backgroundColor: 'rgba(30, 30, 30, 1)' }}
        >
          <div className="absolute top-0 left-0 w-1 h-full" style={{ backgroundColor: '#1976d2' }} />
          <div className="px-3">
            <div className="flex items-center justify-between">
              <div>
                <h2 className="text-base font-medium text-white">
                  Live Transaction Feed
                </h2>
                <p className="text-xs text-gray-300 mt-0.5">
                  Real-time updates from your Bitcoin node
                </p>
              </div>

              {/* Auto Refresh Toggle */}
              <label className="flex items-center gap-3 cursor-pointer">
                <span className="text-sm text-gray-300">Auto Refresh</span>
                <div className="relative">
                  <input
                    type="checkbox"
                    checked={autoRefresh}
                    onChange={handleAutoRefreshChange}
                    className="sr-only peer"
                  />
                  <div className="w-11 h-6 bg-gray-700 rounded-full peer peer-checked:bg-blue-600 peer-focus:ring-2 peer-focus:ring-blue-500 peer-focus:ring-offset-2 peer-focus:ring-offset-gray-900 transition-colors">
                    <div className="absolute top-0.5 left-0.5 bg-white w-5 h-5 rounded-full transition-transform peer-checked:translate-x-5"></div>
                  </div>
                </div>
              </label>
            </div>
          </div>
        </div>

        {/* Error Message */}
        {error && (
          <div className="mb-6 p-4 bg-red-500/10 border border-red-500/20 rounded-lg">
            <div className="flex items-start gap-3">
              <svg
                className="w-5 h-5 text-red-400 mt-0.5 flex-shrink-0"
                fill="none"
                stroke="currentColor"
                viewBox="0 0 24 24"
              >
                <path
                  strokeLinecap="round"
                  strokeLinejoin="round"
                  strokeWidth={2}
                  d="M12 8v4m0 4h.01M21 12a9 9 0 11-18 0 9 9 0 0118 0z"
                />
              </svg>
              <div className="flex-1">
                <p className="text-sm font-medium text-red-400">{error}</p>
                <button
                  onClick={fetchTransactions}
                  className="text-sm text-red-300 underline mt-2 hover:text-red-200"
                >
                  Try again
                </button>
              </div>
            </div>
          </div>
        )}

        {/* Table */}
        <TransactionTable
          transactions={transactions}
          loading={loading}
          error={error}
          autoRefresh={autoRefresh}
          refreshInterval={refreshInterval}
          maxHeight={700}
        />
      </div>
    </div>
  );
};

export default TransactionsPage;
