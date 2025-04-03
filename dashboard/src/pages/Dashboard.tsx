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
import BraidStats from '../components/BraidStats';
import Header from '../components/Header';
import {
  PrimaryMetrics,
  SecondaryMetrics,
} from '../components/DashboardMetrics';
import { BraidVisualizationData } from '../types/braid';
import {
  loadSampleBraidData,
  transformBraidData,
} from '../utils/braidDataTransformer';
import Card from '../components/common/Card';
import colors from '../theme/colors';

// Sidebar icons
import DashboardIcon from '@mui/icons-material/Dashboard';
import ComputerIcon from '@mui/icons-material/Computer';
import PeopleIcon from '@mui/icons-material/People';
import WarningIcon from '@mui/icons-material/Warning';
import SecurityIcon from '@mui/icons-material/Security';
import BarChartIcon from '@mui/icons-material/BarChart';
import AccountBalanceWalletIcon from '@mui/icons-material/AccountBalanceWallet';
import InventoryIcon from '@mui/icons-material/Inventory';

const Dashboard: React.FC = () => {
  const [data, setData] = useState<BraidVisualizationData | null>(null);
  const [loading, setLoading] = useState<boolean>(true);
  const [error, setError] = useState<string | null>(null);
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
          backgroundColor: '#f8f9fa',
          borderRight: '1px solid #eee',
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
          selected
          sx={{
            pl: 2,
            py: 1.5,
            borderLeft: '4px solid #1976d2',
            '&.Mui-selected': {
              backgroundColor: 'rgba(25, 118, 210, 0.08)',
            },
          }}>
          <ListItemIcon sx={{ minWidth: 40 }}>
            <DashboardIcon fontSize='small' />
          </ListItemIcon>
          <ListItemText
            primary='Dashboard'
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>
        <ListItemButton sx={{ pl: 2, py: 1.5 }}>
          <ListItemIcon sx={{ minWidth: 40 }}>
            <ComputerIcon fontSize='small' />
          </ListItemIcon>
          <ListItemText
            primary='Miners'
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>
        <ListItemButton sx={{ pl: 2, py: 1.5 }}>
          <ListItemIcon sx={{ minWidth: 40 }}>
            <PeopleIcon fontSize='small' />
          </ListItemIcon>
          <ListItemText
            primary='Workers'
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>
        <ListItemButton sx={{ pl: 2, py: 1.5 }}>
          <ListItemIcon sx={{ minWidth: 40 }}>
            <WarningIcon fontSize='small' />
          </ListItemIcon>
          <ListItemText
            primary='Issues'
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>
        <ListItemButton sx={{ pl: 2, py: 1.5 }}>
          <ListItemIcon sx={{ minWidth: 40 }}>
            <SecurityIcon fontSize='small' />
          </ListItemIcon>
          <ListItemText
            primary='Security'
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>
        <ListItemButton sx={{ pl: 2, py: 1.5 }}>
          <ListItemIcon sx={{ minWidth: 40 }}>
            <BarChartIcon fontSize='small' />
          </ListItemIcon>
          <ListItemText
            primary='Pools'
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>
        <ListItemButton sx={{ pl: 2, py: 1.5 }}>
          <ListItemIcon sx={{ minWidth: 40 }}>
            <AccountBalanceWalletIcon fontSize='small' />
          </ListItemIcon>
          <ListItemText
            primary='Earnings'
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>
        <ListItemButton sx={{ pl: 2, py: 1.5 }}>
          <ListItemIcon sx={{ minWidth: 40 }}>
            <InventoryIcon fontSize='small' />
          </ListItemIcon>
          <ListItemText
            primary='Assets'
            primaryTypographyProps={{ fontSize: '0.875rem' }}
          />
        </ListItemButton>
      </List>
    </Drawer>
  );

  const mainContent = (
    <Box
      sx={{
        flexGrow: 1,
        p: 3,
        mt: '50px',
        pb: 6, // Add extra bottom padding to avoid footer overlap
        mb: 4, // Add additional bottom margin
      }}>
      {loading ? (
        <Box
          sx={{
            display: 'flex',
            justifyContent: 'center',
            alignItems: 'center',
            height: '50vh',
          }}>
          <CircularProgress />
          <Typography variant='h6' sx={{ ml: 2 }}>
            Loading Data...
          </Typography>
        </Box>
      ) : error ? (
        <Alert severity='error' sx={{ mt: 2 }}>
          {error}
        </Alert>
      ) : (
        data && (
          <>
            {/* Metrics Section */}
            <PrimaryMetrics />
            <SecondaryMetrics />

            {/* Charts Section */}
            <Box sx={{ mt: 4 }}>
              {/* Pool Stats Chart */}
              <Box sx={{ mb: 4 }}>
                <Card
                  title='Pool Statistics'
                  subtitle='Updated every 5 minutes'
                  accentColor={colors.cardAccentPrimary}>
                  <Box
                    sx={{
                      height: 'auto',
                      maxHeight: '400px',
                      position: 'relative',
                    }}>
                    <BraidVisualization
                      data={data}
                      width={
                        window.innerWidth > 1200
                          ? 1100
                          : window.innerWidth - 250
                      }
                      height={300}
                    />
                  </Box>
                </Card>
              </Box>

              {/* Live Worker Stats */}
              <Box>
                <Card
                  title={
                    <Box sx={{ display: 'flex', alignItems: 'center' }}>
                      <Box
                        component='span'
                        sx={{
                          width: 8,
                          height: 8,
                          borderRadius: '50%',
                          bgcolor: colors.success,
                          mr: 1,
                          animation: 'pulse 2s infinite',
                          '@keyframes pulse': {
                            '0%': { opacity: 1 },
                            '50%': { opacity: 0.6 },
                            '100%': { opacity: 1 },
                          },
                        }}
                      />
                      LIVE: ASIC Worker Real-Time Stats (1-min)
                    </Box>
                  }
                  accentColor={colors.cardAccentSuccess}>
                  <Box
                    sx={{
                      height: 'auto',
                      pb: 3,
                    }}>
                    <BraidStats data={data} />
                  </Box>
                </Card>
              </Box>
            </Box>
          </>
        )
      )}
    </Box>
  );

  return (
    <Box
      sx={{
        display: 'flex',
        flexDirection: 'column',
        backgroundColor: colors.background,
        minHeight: '100vh',
      }}>
      <Header />
      <Box sx={{ display: 'flex' }}>
        {sidebar}
        {mainContent}
      </Box>
    </Box>
  );
};

export default Dashboard;
