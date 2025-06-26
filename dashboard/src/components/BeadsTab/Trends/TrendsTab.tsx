import { useState } from 'react';
import { motion } from 'framer-motion';
import { Zap, Activity, Database } from 'lucide-react';
import { useChartData } from '../Hooks/useChartData';
import HashrateTab from './HashrateTab';
import LatencyTab from './LatencyTab';
import TransactionsTab from './TransactionsTab';

export function TrendsTab({ timeRange }: { timeRange: string }) {
  const [activeSubTab, setActiveSubTab] = useState('hashrate');
  const { data: chartData, isLoading: isChartLoading } =
    useChartData(timeRange);
  const [chartHovered, setChartHovered] = useState(false);

  return (
    <div className="space-y-8">
      {/* Subtabs */}
      <div className="flex border-b border-gray-800/70 mb-6">
        {[
          {
            id: 'hashrate',
            label: 'Hashrate',
            icon: <Zap className="w-4 h-4" />,
          },
          {
            id: 'latency',
            label: 'Latency',
            icon: <Activity className="w-4 h-4" />,
          },
          {
            id: 'transactions',
            label: 'Transactions',
            icon: <Database className="w-4 h-4" />,
          },
        ].map((tab) => (
          <motion.button
            key={tab.id}
            className={`flex items-center gap-2 px-4 py-3 font-medium relative ${
              activeSubTab === tab.id
                ? 'text-blue-400'
                : 'text-gray-400 hover:text-gray-200'
            }`}
            onClick={() => setActiveSubTab(tab.id)}
            whileHover={{ y: -2 }}
            whileTap={{ scale: 0.97 }}
          >
            {tab.icon}
            {tab.label}
            {activeSubTab === tab.id && (
              <motion.div
                className="absolute bottom-0 left-0 right-0 h-0.5 bg-blue-500"
                layoutId="activeSubTab"
                initial={{ opacity: 0 }}
                animate={{ opacity: 1 }}
                transition={{ type: 'spring', stiffness: 300, damping: 30 }}
              />
            )}
          </motion.button>
        ))}
      </div>

      {activeSubTab === 'hashrate' && (
        <HashrateTab
          chartData={chartData}
          isChartLoading={isChartLoading}
          chartHovered={chartHovered}
          setChartHovered={setChartHovered}
          timeRange={timeRange}
        />
      )}

      {activeSubTab === 'latency' && (
        <LatencyTab
          chartData={chartData}
          isChartLoading={isChartLoading}
          chartHovered={chartHovered}
          setChartHovered={setChartHovered}
          timeRange={timeRange}
        />
      )}

      {activeSubTab === 'transactions' && (
        <TransactionsTab
          chartData={chartData}
          isChartLoading={isChartLoading}
          chartHovered={chartHovered}
          setChartHovered={setChartHovered}
          timeRange={timeRange}
        />
      )}
    </div>
  );
}
