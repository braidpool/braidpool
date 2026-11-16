import { useNavigate, useParams } from 'react-router-dom';
import Card from '../common/Card';
import Header from '../common/Header';
import MinerInventoryDashboard from '../MinerInventory/MinerInventoryDashboard';
import MempoolLatencyStats from '../Mempool/MempoolLatencyStats';
import { PoolDominance } from '../BeadsTab/PoolDominance/PoolDominance';
import { TrendsTab } from '../BeadsTab/Trends/TrendsTab';
import { RewardsDashboard } from '../BeadsTab/Reward/RewardsDashboard';
import { DEFAULT_TIME_RANGE } from '../BeadsTab/Constants';
import GraphVisualization from '../BraidPoolDAG/BraidPoolDAG';
import NodeHealth from '../NodeHealth/NodeHealth';
import BitcoinStats from '../BitcoinStats/BitcoinStats';
import { Page } from '../common/Types';
import BlockViewer from './BlockViewer';

const Dashboard = () => {
  const navigate = useNavigate();
  const { page } = useParams<{ page?: string }>();

  const getPageFromRoute = (routePage?: string): Page => {
    if (!routePage) return Page.DASHBOARD;

    return Object.values(Page).includes(routePage as Page)
      ? (routePage as Page)
      : Page.DASHBOARD;
  };

  const currentPage = getPageFromRoute(page);
  const setCurrentPage = (nextPage: Page) => {
    const nextPath = `/${nextPage}`;
    navigate(nextPath);
  };

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
      case Page.POOL_DOMINANCE:
        return (
          <div className="p-2">
            <Card title="Pool Dominance">
              <PoolDominance />
            </Card>
          </div>
        );
      case Page.NODE_HEALTH:
        return <NodeHealth />;
      case Page.DAG:
        return (
          <div className="p-2">
            <Card title="Braid DAG">
              <GraphVisualization />
            </Card>
          </div>
        );
      case Page.TRENDS:
        return (
          <div className="p-2">
            <Card title="Network Trends">
              <TrendsTab timeRange={DEFAULT_TIME_RANGE} />
            </Card>
          </div>
        );
      case Page.REWARDS:
        return (
          <div className="p-2">
            <Card title="Rewards">
              <RewardsDashboard />
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
