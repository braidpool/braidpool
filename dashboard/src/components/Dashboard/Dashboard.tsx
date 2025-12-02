import { useState, useEffect, useRef } from 'react';
import {
  Box,
  Divider,
  Drawer,
  List,
  ListItemButton,
  ListItemIcon,
  ListItemText,
  Typography,
} from '@mui/material';
import colors from '../../theme/colors';

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
const drawerWidth = 240;

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
  const [mobileOpen, setMobileOpen] = useState(false);
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
        // Load sample data
        const braidData = await loadSampleBraidData();
        // Transform data for visualization
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

  const handleDrawerToggle = () => {
    setMobileOpen(!mobileOpen);
  };

  // Sidebar drawer content
  const sidebar = (
    <Drawer
      variant="permanent"
      sx={{
        display: { xs: 'none', sm: 'block' },
        '& .MuiDrawer-paper': {
          boxSizing: 'border-box',
          width: drawerWidth,
          backgroundColor: colors.paper,
          borderRight: `1px solid ${colors.border}`,
        },
      }}
      open
    >
      <Box sx={{ p: 2 }}>
        <Typography variant="h6" color="primary" sx={{ fontWeight: 700 }}>
          Braidpool
        </Typography>
      </Box>
      <Divider sx={{ borderColor: colors.border }} />
      <List>
        <ListItemButton
          onClick={() => setCurrentPage(Page.INSTALLATION)}
          selected={currentPage === Page.INSTALLATION}
          sx={{
            pl: 2,
            py: 1.5,
            borderLeft:
              currentPage === Page.INSTALLATION
                ? `4px solid ${colors.primary}`
                : 'none',
            '&.Mui-selected': {
              backgroundColor: 'rgba(57, 134, 232, 0.08)',
            },
          }}
        >
          <ListItemIcon
            sx={{
              minWidth: 40,
              color:
                currentPage === Page.INSTALLATION
                  ? colors.primary
                  : colors.textSecondary,
            }}
          >
            <ConstructionIcon fontSize="small" />
          </ListItemIcon>
          <ListItemText
            primary="Installation"
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>

        <ListItemButton
          onClick={() => setCurrentPage(Page.DASHBOARD)}
          selected={currentPage === Page.DASHBOARD}
          sx={{
            pl: 2,
            py: 1.5,
            borderLeft:
              currentPage === Page.DASHBOARD
                ? `4px solid ${colors.primary}`
                : 'none',
            '&.Mui-selected': {
              backgroundColor: 'rgba(57, 134, 232, 0.08)',
            },
          }}
        >
          <ListItemIcon
            sx={{
              minWidth: 40,
              color:
                currentPage === Page.DASHBOARD
                  ? colors.primary
                  : colors.textSecondary,
            }}
          >
            <DashboardIcon fontSize="small" />
          </ListItemIcon>
          <ListItemText
            primary="Dashboard"
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>

        <ListItemButton
          onClick={() => setCurrentPage(Page.TRANSACTIONS)}
          selected={currentPage === Page.TRANSACTIONS}
          sx={{
            pl: 2,
            py: 1.5,
            borderLeft:
              currentPage === Page.TRANSACTIONS
                ? `4px solid ${colors.primary}`
                : 'none',
            '&.Mui-selected': {
              backgroundColor: 'rgba(57, 134, 232, 0.08)',
            },
          }}
        >
          <ListItemIcon
            sx={{
              minWidth: 40,
              color:
                currentPage === Page.TRANSACTIONS
                  ? colors.primary
                  : colors.textSecondary,
            }}
          >
            <SwapHorizIcon fontSize="small" />
          </ListItemIcon>
          <ListItemText
            primary="Transactions"
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>

        <ListItemButton
          onClick={() => setCurrentPage(Page.MINER_STATS)}
          selected={currentPage === Page.MINER_STATS}
          sx={{
            pl: 2,
            py: 1.5,
            borderLeft:
              currentPage === Page.MINER_STATS
                ? `4px solid ${colors.primary}`
                : 'none',
            '&.Mui-selected': { backgroundColor: 'rgba(57, 134, 232, 0.08)' },
          }}
        >
          <ListItemIcon
            sx={{
              minWidth: 40,
              color:
                currentPage === Page.MINER_STATS
                  ? colors.primary
                  : colors.textSecondary,
            }}
          >
            <MemoryIcon fontSize="small" />
          </ListItemIcon>
          <ListItemText
            primary="Beads"
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>

        <ListItemButton
          onClick={() => setCurrentPage(Page.MINING_INVENTORY)}
          selected={currentPage === Page.MINING_INVENTORY}
          sx={{
            pl: 2,
            py: 1.5,
            borderLeft:
              currentPage === Page.MINING_INVENTORY
                ? `4px solid ${colors.primary}`
                : 'none',
            '&.Mui-selected': {
              backgroundColor: 'rgba(57, 134, 232, 0.08)',
            },
          }}
        >
          <ListItemIcon
            sx={{
              minWidth: 40,
              color:
                currentPage === Page.MINING_INVENTORY
                  ? colors.primary
                  : colors.textSecondary,
            }}
          >
            <InventoryIcon fontSize="small" />
          </ListItemIcon>
          <ListItemText
            primary="Inventory"
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>

        <ListItemButton
          onClick={() => setCurrentPage(Page.MEMPOOL)}
          selected={currentPage === Page.MEMPOOL}
          sx={{
            pl: 2,
            py: 1.5,
            borderLeft:
              currentPage === Page.MEMPOOL
                ? `4px solid ${colors.primary}`
                : 'none',
            '&.Mui-selected': {
              backgroundColor: 'rgba(57, 134, 232, 0.08)',
            },
          }}
        >
          <ListItemIcon
            sx={{
              minWidth: 40,
              color:
                currentPage === Page.MEMPOOL
                  ? colors.primary
                  : colors.textSecondary,
            }}
          >
            <MemoryIcon fontSize="small" />
          </ListItemIcon>
          <ListItemText
            primary="Mempool"
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>

        <ListItemButton
          onClick={() => setCurrentPage(Page.DAG_VISUALIZATION)}
          selected={currentPage === Page.DAG_VISUALIZATION}
          sx={{
            pl: 2,
            py: 1.5,
            borderLeft:
              currentPage === Page.DAG_VISUALIZATION
                ? `4px solid ${colors.primary}`
                : 'none',
            '&.Mui-selected': {
              backgroundColor: 'rgba(57, 134, 232, 0.08)',
            },
          }}
        >
          <ListItemIcon
            sx={{
              minWidth: 40,
              color:
                currentPage === Page.DAG_VISUALIZATION
                  ? colors.primary
                  : colors.textSecondary,
            }}
          >
            <LayersIcon fontSize="small" />
          </ListItemIcon>
          <ListItemText
            primary="Visualize"
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>
      </List>
    </Drawer>
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
            <Box sx={{ display: 'flex', flexWrap: 'wrap', mt: 2, mx: -1 }}>
              <Box sx={{ width: { xs: '100%', md: '50%' }, p: 1 }}>
                <Card title="Pool Hashrate">
                  <PoolHashrateChart loading={loading} />
                </Card>
              </Box>
              <Box sx={{ width: { xs: '100%', md: '50%' }, p: 1 }}>
                <Card title="Mempool Activity">
                  <MempoolLatencyStats />
                </Card>
              </Box>
            </Box>
            <Box sx={{ mt: 2, mx: -1 }}>
              <Box sx={{ p: 1 }}>
                <Card title="Recent Blocks">
                  <RecentBlocksTable />
                </Card>
              </Box>
            </Box>
          </>
        );
      case Page.TRANSACTIONS:
        return <TransactionsPage />;
      case Page.MINING_INVENTORY:
        return <MineInventoryDashboard />;
      case Page.MEMPOOL:
        return (
          <Box sx={{ p: 1 }}>
            <Card title="Mempool Statistics">
              <MempoolLatencyStats />
            </Card>
          </Box>
        );
      case Page.DAG_VISUALIZATION:
        return (
          <Box sx={{ p: 1 }}>
            <Card title="Braid Visualization">
              <Box>
                <GraphVisualization />
              </Box>
            </Card>
          </Box>
        );
      case Page.MINER_STATS:
        return <MinedSharesExplorer />;
      default:
        return (
          <Box sx={{ p: 1 }}>
            <Typography>Coming soon</Typography>
          </Box>
        );
    }
  };

  return (
    <Box sx={{ display: 'flex', minHeight: '100vh' }}>
      <Header title="Braidpool" />
      {sidebar}
      <Box
        component="main"
        sx={{
          flexGrow: 1,
          p: 3,
          width: { sm: `calc(100% - ${drawerWidth}px)` },
          ml: { sm: `${drawerWidth}px` },
          mt: '50px', // Adjust for header height
        }}
      >
        {renderPage()}
      </Box>
    </Box>
  );
};

export default Dashboard;