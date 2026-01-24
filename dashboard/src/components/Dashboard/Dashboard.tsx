import { useState, useEffect, useRef } from 'react';
import Card from '../common/Card';
import Header from '../common/Header';
import MinerInventoryDashboard from '../MinerInventory/MinerInventoryDashboard';
import MempoolLatencyStats from '../Mempool/MempoolLatencyStats';
import GraphVisualization from '../BraidPoolDAG/BraidPoolDAG';
import MinedSharesExplorer from '../BeadsTab/MinedSharesExplorer';
import NodeHealth from '../NodeHealth/NodeHealth';
import BitcoinStats from '../BitcoinStats/BitcoinStats';
import { Page } from './Types';
import BlockViewer from './BlockViewer';
import { TABS } from '../BeadsTab/lib/Constants';

const Dashboard = () => {
  const [currentPage, setCurrentPage] = useState<Page>(Page.DASHBOARD);
  const [activeTab, setActiveTab] = useState('beads');
  const [isDropdownOpen, setIsDropdownOpen] = useState(false);
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

  // Render the main content based on selected page
  const renderPage = () => {
    switch (currentPage) {
      case Page.DASHBOARD:
        return (
          <Card
            title="Braidpool Dashboard"
            subtitle="Welcome to the Braidpool dashboard!"
          >
            <BlockViewer />
          </Card>
        );
      case Page.MINING_INVENTORY:
        return (
          <div className="p-2">
            <Card title="Miner Inventory">
              <MinerInventoryDashboard />
            </Card>
          </div>
        );
      case Page.MEMPOOL:
        return (
          <div className="p-2">
            <Card title="Mempool Statistics">
              <MempoolLatencyStats />
            </Card>
          </div>
        );
      case Page.DAG_VISUALIZATION:
        return (
          <div className="p-2">
            <Card title="Braid Visualization">
              <div>
                <GraphVisualization />
              </div>
            </Card>
          </div>
        );
      case Page.BITCOIN_STATS:
        return (
          <div className="p-2">
            <Card title="Bitcoin Statistics">
              <div>
                <BitcoinStats />
              </div>
            </Card>
          </div>
        );
      case Page.MINER_STATS:
        return (
          <div className="p-2">
            <Card
              title="Beads Explorer"
              headerExtra={
                <div className="relative">
                  <label htmlFor="beads-explorer-tabs" className="sr-only">
                    Select a beads view
                  </label>

                  <div
                    className="relative block sm:hidden min-w-[150px]"
                    ref={dropdownRef}
                  >
                    <button
                      type="button"
                      className="flex w-full items-center justify-between rounded-md border border-gray-700 bg-gray-800 py-1 px-3 text-sm text-white focus:border-blue-500 focus:outline-none focus:ring-1 focus:ring-blue-500"
                      onClick={() => setIsDropdownOpen(!isDropdownOpen)}
                    >
                      <span>{TABS.find((t) => t.id === activeTab)?.label}</span>
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
                        {TABS.filter((tab) => tab.id !== activeTab).map(
                          (tab) => (
                            <button
                              key={tab.id}
                              className="block w-full text-left px-3 py-2 text-sm text-white hover:bg-gray-700 transition-colors"
                              onClick={() => {
                                setActiveTab(tab.id);
                                setIsDropdownOpen(false);
                              }}
                            >
                              {tab.label}
                            </button>
                          )
                        )}
                      </div>
                    )}
                  </div>
                </div>
              }
            >
              <div>
                <MinedSharesExplorer
                  activeTab={activeTab}
                  setActiveTab={setActiveTab}
                />
              </div>
            </Card>
          </div>
        );
      case Page.NODE_HEALTH:
        return (
          <div className="p-2">
            <Card title="Node Health Dashboard">
              <div>
                <NodeHealth />
              </div>
            </Card>
          </div>
        );

      default:
        return (
          <div className="p-2">
            <span>Coming soon</span>
          </div>
        );
    }
  };

  return (
    <div className="min-h-screen bg-[#121212]">
      <Header
        title="Braidpool"
        currentPage={currentPage}
        setCurrentPage={setCurrentPage}
      />
      <main
        className="flex-grow w-full pt-16 px-3 md:px-8"
        style={{ minHeight: 'calc(100vh - 56px)' }}
      >
        {renderPage()}
      </main>
    </div>
  );
};

export default Dashboard;
