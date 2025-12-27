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
      {/* Navigation Area */}
      <div className="border-b border-gray-800">
        
        {/* Mobile View: Dropdown (Hidden on medium screens and up) */}
        <div className="md:hidden mb-4 px-2">
          <label htmlFor="tabs" className="sr-only">
            Select a tab
          </label>
          <div className="relative">
            <select
              id="tabs"
              name="tabs"
              className="block w-full rounded-md border border-gray-700 bg-gray-800 py-2 pl-3 pr-3 text-base text-white focus:border-blue-500 focus:outline-none focus:ring-blue-500  sm:text-sm appearance-none"
              value={activeSubTab}
              onChange={(e) => setActiveSubTab(e.target.value)}
            >
              {TrendsTABS.map((tab) => (
                <option key={tab.id} value={tab.id}>
                  {tab.label}
                </option>
              ))}
            </select>
            {/* Custom downward arrow for style consistency */}
            <div className="pointer-events-none absolute inset-y-0 right-0 flex items-center px-4 text-gray-400">
                <svg className="h-4 w-4 fill-current" xmlns="http://www.w3.org/2000/svg" viewBox="0 0 20 20">
                    <path fillRule="evenodd" d="M5.293 7.293a1 1 0 011.414 0L10 10.586l3.293-3.293a1 1 0 111.414 1.414l-4 4a1 1 0 01-1.414 0l-4-4a1 1 0 010-1.414z" clipRule="evenodd" />
                </svg>
            </div>
          </div>
        </div>

        {/* Desktop View: Tabs (Hidden on small screens, Flex on medium+) */}
        <nav
          className="!hidden md:!flex -mb-px flex-wrap justify-center gap-x-10"
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

      {/* Content Sections */}
      <div className={activeSubTab === 'hashrate' ? 'block' : 'hidden'}>
        <HashrateTab timeRange={timeRange} />
      </div>
      <div className={activeSubTab === 'latency' ? 'block' : 'hidden'}>
        <LatencyTab timeRange={timeRange} />
      </div>
      <div
        className={activeSubTab === 'transactions' ? 'block' : 'hidden'}
      >
        <TransactionsTab
          chartHovered={chartHovered}
          setChartHovered={setChartHovered}
          timeRange={timeRange}
        />
      </div>
      <div
        className={activeSubTab === 'difficulty' ? 'block' : 'hidden'}
      >
        <Difficulty />
      </div>
    </div>
  );
}