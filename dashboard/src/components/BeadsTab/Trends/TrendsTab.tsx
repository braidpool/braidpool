import { useState } from 'react';
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
      <div className="flex border-b mb-6 bg-[#1c1c1c]">
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
          <button
            key={tab.id}
            className={`flex items-center gap-2 px-4 py-3 font-medium relative ${
              activeSubTab === tab.id
                ? 'text-blue-400 border-b-2 border-blue-500'
                : 'text-gray-400 hover:text-gray-200'
            }`}
            onClick={() => setActiveSubTab(tab.id)}
          >
            {tab.icon}
            {tab.label}
          </button>
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
