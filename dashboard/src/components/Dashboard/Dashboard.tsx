import { useState, useEffect } from 'react';
import TopStatsBar from '../common/TopStatsBar';
import Card from '../common/Card';
import Header from '../common/Header';
import InstallationInstructions from '../Installation/InstallationInstructions';
import MineInventoryDashboard from '../MinerInventory/MineInventoryDashboard';
import PoolHashrateChart from './PoolHashrateChart';
import MempoolLatencyStats from './MempoolLatencyStats';
import RecentBlocksTable from './RecentBlocksTable';
import GraphVisualization from '../BraidPoolDAG/BraidPoolDAG';
import MinedSharesExplorer from '../BeadsTab/MinedSharesExplorer';

import { loadSampleBraidData } from '../../utils/braidDataTransformer';
import BitcoinStats from '../BitcoinStats/BitcoinStats';
import { Page } from './Types';

const Dashboard = () => {
  const [loading, setLoading] = useState(true);
  const [currentPage, setCurrentPage] = useState<Page>(Page.DASHBOARD);

  useEffect(() => {
    const fetchData = async () => {
      try {
        setLoading(true);
        await loadSampleBraidData();
      } finally {
        setLoading(false);
      }
    };
    fetchData();
  }, []);

  // Render the main content based on selected page
  const renderPage = () => {
    switch (currentPage) {
      case Page.INSTALLATION:
        return <InstallationInstructions />;
      case Page.DASHBOARD:
        return (
          <>
            <TopStatsBar loading={loading} />
            <div className="flex flex-wrap mt-2 -mx-2">
              <div className="w-full md:w-1/2 p-2">
                <Card title="Pool Hashrate">
                  <PoolHashrateChart loading={loading} />
                </Card>
              </div>
              <div className="w-full md:w-1/2 p-2">
                <Card title="Mempool Activity">
                  <MempoolLatencyStats />
                </Card>
              </div>
            </div>
            <div className="mt-2 -mx-2">
              <div className="p-2">
                <Card title="Recent Blocks">
                  <RecentBlocksTable />
                </Card>
              </div>
            </div>
          </>
        );
      case Page.MINING_INVENTORY:
        return <MineInventoryDashboard />;
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
        return <MinedSharesExplorer />;
      default:
        return (
          <div className="p-2">
            <span>Coming soon</span>
          </div>
        );
    }
  };

  return (
    <div className="min-h-screen bg-[#0e1621]">
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
