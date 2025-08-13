import { useState } from 'react';
import { TrendsTABS } from '../lib/Constants';
import HashrateTab from './HashrateTab';
import LatencyTab from './LatencyTab';
import TransactionsTab from './TransactionsTab';
import { Difficulty } from './Difficulty';

export function TrendsTab({ timeRange }: { timeRange: string }) {
  const [activeSubTab, setActiveSubTab] = useState('hashrate');
  const [chartHovered, setChartHovered] = useState(false);

  return (
    <div className="space-y-8">
      {/* Subtabs */}
      <div className="border-b border-gray-800">
        <nav
          className="-mb-px flex flex-wrap justify-center gap-x-10"
          aria-label="Tabs"
        >
          {TrendsTABS.map((tab) => (
            <button
              key={tab.id}
              onClick={() => setActiveSubTab(tab.id)}
              className={`
                group inline-flex items-center gap-2 whitespace-nowrap py-3 px-1 border-b-2
                font-medium text-sm transition-all duration-200
                ${
                  activeSubTab === tab.id
                    ? 'border-blue-500 text-blue-400'
                    : 'border-transparent text-white hover:border-gray-300'
                }
              `}
            >
              <tab.icon
                className={`w-4 h-4 transition-colors duration-200 ${
                  activeSubTab === tab.id
                    ? 'text-blue-400'
                    : 'text-gray-500 group-hover:text-white'
                }`}
              />
              {tab.label}
            </button>
          ))}
        </nav>
      </div>

      <div style={{ display: activeSubTab === 'hashrate' ? 'block' : 'none' }}>
        <HashrateTab timeRange={timeRange} />
      </div>
      <div style={{ display: activeSubTab === 'latency' ? 'block' : 'none' }}>
        <LatencyTab timeRange={timeRange} />
      </div>
      <div
        style={{ display: activeSubTab === 'transactions' ? 'block' : 'none' }}
      >
        <TransactionsTab
          chartHovered={chartHovered}
          setChartHovered={setChartHovered}
          timeRange={timeRange}
        />
      </div>
      <div
        style={{ display: activeSubTab === 'difficulty' ? 'block' : 'none' }}
      >
        <Difficulty />
      </div>
    </div>
  );
}
