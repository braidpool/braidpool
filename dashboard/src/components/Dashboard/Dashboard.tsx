import { useState, useEffect } from 'react';

// Icons
import {
  MdDashboard as DashboardIcon,
  MdConstruction as ConstructionIcon,
  MdInventory as InventoryIcon,
  MdMemory as MemoryIcon,
  MdLayers as LayersIcon,
  MdSwapHoriz as SwapHorizIcon
} from 'react-icons/md';

// Components
import TopStatsBar from '../common/TopStatsBar';
import Card from '../common/Card';
import Header from '../common/Header';
import InstallationInstructions from '../Installation/InstallationInstructions';
import MineInventoryDashboard from '../MinerDashboard/MineInventoryDashboard';
import PoolHashrateChart from './PoolHashrateChart';
import MempoolLatencyStats from './MempoolLatencyStats';
import RecentBlocksTable from './RecentBlocksTable';
import GraphVisualization from '../BraidPoolDAG/BraidPoolDAG';
import MinedSharesExplorer from '../MinerDashboard/MinedSharesExplorer';
import TransactionsPage from '../Transactions/TransactionsPage';

// Utils
import {
  loadSampleBraidData,
  transformBraidData,
} from '../../utils/braidDataTransformer';

// Constants
const DRAWER_WIDTH = 240;

// Define available pages as an enum
enum Page {
  INSTALLATION = 'installation',
  DASHBOARD = 'dashboard',
  TRANSACTIONS = 'transactions',
  MINING_INVENTORY = 'mining-inventory',
  MEMPOOL = 'mempool',
  DAG_VISUALIZATION = 'dag-visualization',
  MINER_STATS = 'miner-stats',
}

const Dashboard = () => {
  const [_data, setData] = useState<any>(null);
  const [loading, setLoading] = useState(true);
  const [_error, setError] = useState<string | null>(null);
  const [currentPage, setCurrentPage] = useState<Page>(Page.DASHBOARD);

  // Fetch data when component mounts
  useEffect(() => {
    const fetchData = async () => {
      try {
        console.log('🔄 Loading braid data...');
        setLoading(true);
        setError(null);
        const braidData = await loadSampleBraidData();
        const transformedData = transformBraidData(braidData);
        setData(transformedData);
        console.log('✅ Data loaded successfully!');
      } catch (err) {
        console.error('❌ Error loading data:', err);
        setError('Failed to load data. Please try again later.');
      } finally {
        setLoading(false);
      }
    };
    fetchData();
  }, []);

  // Navigation items
  const navItems = [
    { id: Page.INSTALLATION, label: 'Installation', icon: ConstructionIcon },
    { id: Page.DASHBOARD, label: 'Dashboard', icon: DashboardIcon },
    { id: Page.TRANSACTIONS, label: 'Transactions', icon: SwapHorizIcon },
    { id: Page.MINER_STATS, label: 'Beads', icon: MemoryIcon },
    { id: Page.MINING_INVENTORY, label: 'Inventory', icon: InventoryIcon },
    { id: Page.MEMPOOL, label: 'Mempool', icon: MemoryIcon },
    { id: Page.DAG_VISUALIZATION, label: 'Visualize', icon: LayersIcon },
  ];

  // Sidebar drawer content
  const sidebar = (
    <div className="fixed left-0 top-0 h-full w-60 bg-[#1e1e1e] border-r border-[#2d2d2d] z-10">
      <div className="p-4">
        <h1 className="text-xl font-bold text-white">Braidpool</h1>
      </div>
      <hr className="border-[#2d2d2d]" />
      <nav className="mt-2">
        {navItems.map((item) => {
          const Icon = item.icon;
          const isSelected = currentPage === item.id;
          return (
            <button
              key={item.id}
              onClick={() => setCurrentPage(item.id)}
              className={`w-full flex items-center px-4 py-3 text-sm transition-colors cursor-pointer ${isSelected
                ? 'bg-[#2d4a6b] border-l-4 border-[#5b9bd5] text-white'
                : 'text-gray-300 hover:bg-[#2a2a2a] border-l-4 border-transparent'
                }`}
            >
              <Icon className="w-5 h-5 mr-3 flex-shrink-0" />
              <span className="text-left">{item.label}</span>
            </button>
          );
        })}
      </nav>
    </div>
  );

  // Render the main content based on selected page
  const renderPage = () => {
    switch (currentPage) {
      case Page.INSTALLATION:
        return <InstallationInstructions />;
      case Page.DASHBOARD:
        return (
          <>
            <TopStatsBar loading={loading} />
            <div className="flex flex-wrap mt-4 -mx-2">
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
            <div className="mt-4 -mx-2">
              <div className="p-2">
                <Card title="Recent Blocks">
                  <RecentBlocksTable />
                </Card>
              </div>
            </div>
          </>
        );
      case Page.TRANSACTIONS:
        return <TransactionsPage />;
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
      case Page.MINER_STATS:
        return <MinedSharesExplorer />;
      default:
        return (
          <div className="p-2">
            <p className="text-gray-400">Coming soon</p>
          </div>
        );
    }
  };

  return (
    <div className="flex min-h-screen bg-[#0f1419]">
      <Header title="Braidpool" />
      {sidebar}
      <main className="flex-1 p-6 ml-60 mt-12">
        {renderPage()}
      </main>
    </div>
  );
};

export default Dashboard;