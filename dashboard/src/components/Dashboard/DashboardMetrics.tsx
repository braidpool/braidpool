import React from 'react';
import { Box, Typography } from '@mui/material';
import KPICard from '../common/KPICard';
import MemoryIcon from '@mui/icons-material/Memory';
import AccountBalanceWalletIcon from '@mui/icons-material/AccountBalanceWallet';
import DeviceHubIcon from '@mui/icons-material/DeviceHub';
import PublicIcon from '@mui/icons-material/Public';
import PercentIcon from '@mui/icons-material/Percent';
import AttachmentIcon from '@mui/icons-material/Attachment';
import BlurOnIcon from '@mui/icons-material/BlurOn';
import PriorityHighIcon from '@mui/icons-material/PriorityHigh';

// Mock data for the Braidpool dashboard with realistic values
const mockData = {
  // Primary metrics
  networkHashrate: '725.06',
  difficultyTarget: '8.92e+12',
  beadRate: '4.23',
  estimatedEarnings: '137.20',

  // Secondary metrics
  nbNcRatio: '1.765',
  shareCount: '14,532',
  tipsCount: '4',
  relativeShareValue: '0.028',

  // Other tracking data
  cohortFormationRate: '1.2',
  networkLatency: '215',
};

interface DashboardMetricsProps {
  loading?: boolean;
}

export const PrimaryMetrics: React.FC<DashboardMetricsProps> = ({
  loading = false,
}) => {
  return (
    <Box sx={{ mb: 4 }}>
      <Typography variant='subtitle1' sx={{ mb: 2, fontWeight: 500, px: 1 }}>
        Primary Metrics
      </Typography>
      <Box sx={{ display: 'flex', flexWrap: 'wrap', mx: -1 }}>
        <Box sx={{ width: { xs: '50%', sm: '25%' }, p: 1 }}>
          <KPICard
            title='NETWORK HASHRATE'
            value={mockData.networkHashrate}
            unit='PH/s'
            subtitle='TOTAL NETWORK'
            loading={loading}
            info='Total hashrate of all connected miners in the network'
            icon={<PublicIcon />}
          />
        </Box>
        <Box sx={{ width: { xs: '50%', sm: '25%' }, p: 1 }}>
          <KPICard
            title='DIFFICULTY TARGET'
            value={mockData.difficultyTarget}
            subtitle='CURRENT TARGET'
            loading={loading}
            info='Current target difficulty for bead creation in the Braidpool network'
            icon={<PriorityHighIcon />}
            change={-2.4}
          />
        </Box>
        <Box sx={{ width: { xs: '50%', sm: '25%' }, p: 1 }}>
          <KPICard
            title='BEAD RATE'
            value={mockData.beadRate}
            unit='bps'
            subtitle='BEADS PER SECOND'
            loading={loading}
            info='Current rate of bead creation in the Braidpool network'
            icon={<BlurOnIcon />}
            change={1.7}
          />
        </Box>
        <Box sx={{ width: { xs: '50%', sm: '25%' }, p: 1 }}>
          <KPICard
            title='USD / Day'
            value={mockData.estimatedEarnings}
            subtitle='ESTIMATED EARNINGS'
            loading={loading}
            info='Estimated daily earnings based on your share contribution'
            icon={<AccountBalanceWalletIcon />}
          />
        </Box>
      </Box>
    </Box>
  );
};

export const SecondaryMetrics: React.FC<DashboardMetricsProps> = ({
  loading = false,
}) => {
  return (
    <Box sx={{ mb: 4 }}>
      <Typography variant='subtitle1' sx={{ mb: 2, fontWeight: 500, px: 1 }}>
        Secondary Metrics
      </Typography>
      <Box sx={{ display: 'flex', flexWrap: 'wrap', mx: -1 }}>
        <Box sx={{ width: { xs: '50%', sm: '25%' }, p: 1 }}>
          <KPICard
            title='Nb/Nc RATIO'
            value={mockData.nbNcRatio}
            subtitle='BEADS-TO-COHORTS'
            loading={loading}
            info='Critical consensus metric: ratio of total beads to total cohorts'
            icon={<DeviceHubIcon />}
            change={0.12}
          />
        </Box>
        <Box sx={{ width: { xs: '50%', sm: '25%' }, p: 1 }}>
          <KPICard
            title='SHARE COUNT'
            value={mockData.shareCount}
            subtitle='YOUR CONTRIBUTION'
            loading={loading}
            info='Number of shares you have contributed to the pool'
            icon={<AttachmentIcon />}
            change={3.4}
          />
        </Box>
        <Box sx={{ width: { xs: '50%', sm: '25%' }, p: 1 }}>
          <KPICard
            title='TIPS COUNT'
            value={mockData.tipsCount}
            subtitle='CURRENT TIPS'
            loading={loading}
            info='Current number of tip beads in the braid structure'
            icon={<MemoryIcon />}
          />
        </Box>
        <Box sx={{ width: { xs: '50%', sm: '25%' }, p: 1 }}>
          <KPICard
            title='SHARE VALUE'
            value={mockData.relativeShareValue}
            unit='%'
            subtitle='POOL CONTRIBUTION'
            loading={loading}
            info={`Your percentage of the pool's total rewards`}
            icon={<PercentIcon />}
          />
        </Box>
      </Box>
    </Box>
  );
};

const DashboardMetrics: React.FC<DashboardMetricsProps> = ({
  loading = false,
}) => {
  return (
    <Box>
      <PrimaryMetrics loading={loading} />
      <SecondaryMetrics loading={loading} />
    </Box>
  );
};

export default DashboardMetrics;
