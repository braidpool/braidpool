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

const Dashboard = () => {
  const [currentPage, setCurrentPage] = useState<Page>(Page.DASHBOARD);

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
            <Card title="Beads Explorer">
              <div>
                <MinedSharesExplorer />
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
