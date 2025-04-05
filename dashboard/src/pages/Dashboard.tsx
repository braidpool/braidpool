import React, { useEffect, useState } from 'react';
import {
  Typography,
  Box,
  CircularProgress,
  Alert,
  ListItemButton,
  List,
  ListItemIcon,
  ListItemText,
  Drawer,
} from '@mui/material';
import BraidVisualization from '../components/BraidVisualization';
import Header from '../components/Header';
import { BraidVisualizationData } from '../types/braid';
import {
  loadSampleBraidData,
  transformBraidData,
} from '../utils/braidDataTransformer';
import Card from '../components/common/Card';
import colors from '../theme/colors';
import TopStatsBar from '../components/TopStatsBar';
import PoolHashrateChart from '../components/PoolHashrateChart';
import RecentBlocksTable from '../components/RecentBlocksTable';
import MineInventoryDashboard from '../components/MineInventoryDashboard';
import MempoolLatencyStats from '../components/MempoolLatencyStats';
import InstallationInstructions from '../components/InstallationInstructions';

// Sidebar icons
import DashboardIcon from '@mui/icons-material/Dashboard';
import ComputerIcon from '@mui/icons-material/Computer';
import PeopleIcon from '@mui/icons-material/People';
import WarningIcon from '@mui/icons-material/Warning';
import SecurityIcon from '@mui/icons-material/Security';
import BarChartIcon from '@mui/icons-material/BarChart';
import AccountBalanceWalletIcon from '@mui/icons-material/AccountBalanceWallet';
import InventoryIcon from '@mui/icons-material/Inventory';
import BuildIcon from '@mui/icons-material/Build';
import ExploreIcon from '@mui/icons-material/Explore';
import MemoryIcon from '@mui/icons-material/Memory';
import LayersIcon from '@mui/icons-material/Layers';
import SpeedIcon from '@mui/icons-material/Speed';
import InsertDriveFileIcon from '@mui/icons-material/InsertDriveFile';

// Available pages
enum Page {
  INSTALLATION = 'installation',
  DASHBOARD = 'dashboard',
  MINERS = 'miners',
  MEMPOOL = 'mempool',
  MINING_INVENTORY = 'mining_inventory',
  DAG_VISUALIZATION = 'dag_visualization',
}

const Dashboard: React.FC = () => {
  const [data, setData] = useState<BraidVisualizationData | null>(null);
  const [loading, setLoading] = useState<boolean>(true);
  const [error, setError] = useState<string | null>(null);
  const [currentPage, setCurrentPage] = useState<Page>(Page.DASHBOARD);
  const drawerWidth = 200;

  useEffect(() => {
    const fetchData = async () => {
      try {
        console.log('🔄 Loading braid data...');
        setLoading(true);

        // In a real implementation, this would fetch from an API
        // For now, we'll use sample data
        const braidData = await loadSampleBraidData();
        setData(transformBraidData(braidData));
        console.log('✅ Data loaded successfully!');
        setLoading(false);
      } catch (err) {
        console.error('❌ Error loading data:', err);
        setError('Failed to load data. Please try again later.');
        setLoading(false);
      }
    };

    fetchData();
  }, []);

  // Side navigation
  const sidebar = (
    <Drawer
      variant='permanent'
      sx={{
        width: drawerWidth,
        flexShrink: 0,
        '& .MuiDrawer-paper': {
          width: drawerWidth,
          boxSizing: 'border-box',
          backgroundColor: colors.paper,
          borderRight: `1px solid ${colors.border}`,
          mt: '50px', // Adjusted for header height
          zIndex: (theme) => theme.zIndex.drawer,
        },
      }}>
      <Box sx={{ p: 2, pt: 3, pb: 0 }}>
        <Typography
          variant='subtitle2'
          color='text.secondary'
          sx={{ fontWeight: 'bold', fontSize: '0.75rem', mb: 2, ml: 2 }}>
          NAVIGATION
        </Typography>
      </Box>
      <List sx={{ py: 0 }}>
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
          }}>
          <ListItemIcon
            sx={{
              minWidth: 40,
              color:
                currentPage === Page.INSTALLATION
                  ? colors.primary
                  : colors.textSecondary,
            }}>
            <InsertDriveFileIcon fontSize='small' />
          </ListItemIcon>
          <ListItemText
            primary='Installation'
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
          }}>
          <ListItemIcon
            sx={{
              minWidth: 40,
              color:
                currentPage === Page.DASHBOARD
                  ? colors.primary
                  : colors.textSecondary,
            }}>
            <DashboardIcon fontSize='small' />
          </ListItemIcon>
          <ListItemText
            primary='Dashboard'
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>

        <ListItemButton
          onClick={() => setCurrentPage(Page.MINERS)}
          selected={currentPage === Page.MINERS}
          sx={{
            pl: 2,
            py: 1.5,
            borderLeft:
              currentPage === Page.MINERS
                ? `4px solid ${colors.primary}`
                : 'none',
            '&.Mui-selected': {
              backgroundColor: 'rgba(57, 134, 232, 0.08)',
            },
          }}>
          <ListItemIcon
            sx={{
              minWidth: 40,
              color:
                currentPage === Page.MINERS
                  ? colors.primary
                  : colors.textSecondary,
            }}>
            <ComputerIcon fontSize='small' />
          </ListItemIcon>
          <ListItemText
            primary='Miners'
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
          }}>
          <ListItemIcon
            sx={{
              minWidth: 40,
              color:
                currentPage === Page.MINING_INVENTORY
                  ? colors.primary
                  : colors.textSecondary,
            }}>
            <InventoryIcon fontSize='small' />
          </ListItemIcon>
          <ListItemText
            primary='Inventory'
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
          }}>
          <ListItemIcon
            sx={{
              minWidth: 40,
              color:
                currentPage === Page.MEMPOOL
                  ? colors.primary
                  : colors.textSecondary,
            }}>
            <SpeedIcon fontSize='small' />
          </ListItemIcon>
          <ListItemText
            primary='Mempool & Latency'
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
          }}>
          <ListItemIcon
            sx={{
              minWidth: 40,
              color:
                currentPage === Page.DAG_VISUALIZATION
                  ? colors.primary
                  : colors.textSecondary,
            }}>
            <LayersIcon fontSize='small' />
          </ListItemIcon>
          <ListItemText
            primary='DAG Visualization'
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>

        <Box sx={{ mt: 1, mb: 1, borderTop: `1px solid ${colors.border}` }} />

        <ListItemButton sx={{ pl: 2, py: 1.5 }}>
          <ListItemIcon sx={{ minWidth: 40, color: colors.textSecondary }}>
            <PeopleIcon fontSize='small' />
          </ListItemIcon>
          <ListItemText
            primary='Workers'
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>
        <ListItemButton sx={{ pl: 2, py: 1.5 }}>
          <ListItemIcon sx={{ minWidth: 40, color: colors.textSecondary }}>
            <WarningIcon fontSize='small' />
          </ListItemIcon>
          <ListItemText
            primary='Issues'
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>
        <ListItemButton sx={{ pl: 2, py: 1.5 }}>
          <ListItemIcon sx={{ minWidth: 40, color: colors.textSecondary }}>
            <SecurityIcon fontSize='small' />
          </ListItemIcon>
          <ListItemText
            primary='Security'
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>
        <ListItemButton sx={{ pl: 2, py: 1.5 }}>
          <ListItemIcon sx={{ minWidth: 40, color: colors.textSecondary }}>
            <BarChartIcon fontSize='small' />
          </ListItemIcon>
          <ListItemText
            primary='Pools'
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>
        <ListItemButton sx={{ pl: 2, py: 1.5 }}>
          <ListItemIcon sx={{ minWidth: 40, color: colors.textSecondary }}>
            <AccountBalanceWalletIcon fontSize='small' />
          </ListItemIcon>
          <ListItemText
            primary='Earnings'
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>
      </List>
    </Drawer>
  );

  // Render current page content
  const renderPage = () => {
    if (loading) {
      return (
        <Box
          sx={{
            display: 'flex',
            justifyContent: 'center',
            alignItems: 'center',
            height: '50vh',
          }}>
          <CircularProgress />
          <Typography variant='h6' sx={{ ml: 2, color: colors.textPrimary }}>
            Loading Data...
          </Typography>
        </Box>
      );
    }

    if (error) {
      return (
        <Alert severity='error' sx={{ mt: 2 }}>
          {error}
        </Alert>
      );
    }

    switch (currentPage) {
      case Page.INSTALLATION:
        return <InstallationInstructions />;

      case Page.DASHBOARD:
        return (
          <>
            {/* Top Stats Bar */}
            <TopStatsBar />

            {/* Middle Section - Hashrate Graph and Recent Blocks */}
            <Box
              sx={{
                display: 'flex',
                flexDirection: { xs: 'column', md: 'row' },
                gap: 3,
                mb: 3,
              }}>
              <Box sx={{ flex: { xs: '1 1 100%', md: '1 1 66.67%' } }}>
                <PoolHashrateChart height={350} />
              </Box>
              <Box sx={{ flex: { xs: '1 1 100%', md: '1 1 33.33%' } }}>
                <RecentBlocksTable maxHeight={350} />
              </Box>
            </Box>

            {/* Bottom Section - Mempool Stats */}
            <Box sx={{ mb: 3 }}>
              <MempoolLatencyStats />
            </Box>
          </>
        );

      case Page.MINERS:
        return <TopStatsBar />;

      case Page.MINING_INVENTORY:
        return <MineInventoryDashboard />;

      case Page.MEMPOOL:
        return <MempoolLatencyStats />;

      case Page.DAG_VISUALIZATION:
        return (
          <>
            {/* DAG Visualization */}
            <Card
              title='DAG Visualization'
              subtitle='Directed Acyclic Graph of the braid structure'
              accentColor={colors.cardAccentSuccess}>
              <Box
                sx={{
                  borderRadius: 1,
                  overflow: 'hidden',
                  height: 600,
                  width: '100%',
                }}>
                {data && <BraidVisualization data={data} height={600} />}
              </Box>
            </Card>
          </>
        );

      default:
        return <div>Page not found</div>;
    }
  };

  const mainContent = (
    <Box
      sx={{
        flexGrow: 1,
        p: 3,
        mt: '50px',
        pb: 6, // Add extra bottom padding to avoid footer overlap
        mb: 4, // Add additional bottom margin
        backgroundColor: colors.background,
      }}>
      {renderPage()}
    </Box>
  );

  return (
    <>
      <Header />
      <Box sx={{ display: 'flex' }}>
        {sidebar}
        {mainContent}
      </Box>
    </>
  );
};

export default Dashboard;
