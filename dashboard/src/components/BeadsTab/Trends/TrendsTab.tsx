import { useState, useRef, useEffect } from 'react';
import { TrendsTABS } from '../lib/Constants';
import HashrateTab from './HashrateTab';
import LatencyTab from './LatencyTab';
import TransactionsTab from './TransactionsTab';
import { Difficulty } from './Difficulty';

export function TrendsTab({ timeRange }: { timeRange: string }) {
  const [activeSubTab, setActiveSubTab] = useState('hashrate');
  const [isDropdownOpen, setIsDropdownOpen] = useState(false);
  const [chartHovered, setChartHovered] = useState(false);
  const dropdownRef = useRef<HTMLDivElement>(null);

  useEffect(() => {
    function handleClickOutside(event: MouseEvent) {
      if (
        dropdownRef.current &&
        !dropdownRef.current.contains(event.target as Node)
      ) {
        setIsDropdownOpen(false);
      }
    }
    document.addEventListener('mousedown', handleClickOutside);
    return () => {
      document.removeEventListener('mousedown', handleClickOutside);
    };
  }, []);

  return (
    <div className="space-y-8">
      {/* Navigation Area */}
      <div className="border-b border-gray-800">
        {/* Mobile View: Dropdown (Hidden on medium screens and up) */}
        <div className="md:hidden mb-4 px-2">
          <div className="relative" ref={dropdownRef}>
            <button
              type="button"
              data-testid="mobile-dropdown-trigger"
              className="flex w-full items-center justify-between rounded-md border border-gray-700 bg-gray-800 py-2 pl-3 pr-3 text-base text-white focus:border-blue-500 focus:outline-none focus:ring-1 focus:ring-blue-500 sm:text-sm"
              onClick={() => setIsDropdownOpen(!isDropdownOpen)}
            >
              <div className="flex items-center gap-2">
                {(() => {
                  const activeTab = TrendsTABS.find(
                    (t) => t.id === activeSubTab
                  );
                  if (activeTab) {
                    const Icon = activeTab.icon;
                    return (
                      <>
                        <Icon className="w-4 h-4 text-blue-400" />
                        <span>{activeTab.label}</span>
                      </>
                    );
                  }
                  return null;
                })()}
              </div>
              <svg
                className={`ml-2 h-4 w-4 transition-transform ${
                  isDropdownOpen ? 'rotate-180' : ''
                }`}
                xmlns="http://www.w3.org/2000/svg"
                fill="none"
                viewBox="0 0 24 24"
                stroke="currentColor"
              >
                <path
                  strokeLinecap="round"
                  strokeLinejoin="round"
                  strokeWidth={2}
                  d="M19 9l-7 7-7-7"
                />
              </svg>
            </button>

            {isDropdownOpen && (
              <div className="absolute right-0 top-full mt-1 w-full overflow-hidden rounded-md border border-gray-700 bg-gray-800 shadow-lg z-50">
                {TrendsTABS.map((tab) => (
                  <button
                    key={tab.id}
                    data-testid={`mobile-option-${tab.id}`}
                    className={`flex items-center gap-2 w-full text-left px-3 py-2 text-sm text-white hover:bg-gray-700 transition-colors ${
                      activeSubTab === tab.id
                        ? 'bg-gray-700/50 text-blue-400'
                        : ''
                    }`}
                    onClick={() => {
                      setActiveSubTab(tab.id);
                      setIsDropdownOpen(false);
                    }}
                  >
                    <tab.icon
                      className={`w-4 h-4 ${
                        activeSubTab === tab.id
                          ? 'text-blue-400'
                          : 'text-gray-500'
                      }`}
                    />
                    {tab.label}
                  </button>
                ))}
              </div>
            )}
          </div>
        </div>

        {/* Desktop View: Tabs (Hidden on small screens, Flex on medium+) */}

        <nav
          className="hidden md:flex -mb-px flex-wrap justify-center gap-x-10"
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
