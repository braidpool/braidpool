import { useState, useEffect } from 'react';
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

                  <select
                    id="beads-explorer-tabs"
                    name="beads-explorer-tabs"
                    className="block md:hidden rounded-md border border-gray-700 bg-gray-800 py-1 px-3 text-sm text-white focus:border-blue-500 focus:outline-none focus:ring-blue-500 min-w-[150px]"
                    value={activeTab}
                    onChange={(e) => setActiveTab(e.target.value)}
                  >
                    {TABS.map((tab) => (
                      <option key={tab.id} value={tab.id}>
                        {tab.label}
                      </option>
                    ))}
                  </select>
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
