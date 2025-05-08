import React, { useState } from 'react';
import {
  Box,
  Typography,
  Grid,
  Paper,
  Chip,
  Button,
  Tooltip,
} from '@mui/material';
import colors from '../../theme/colors';
import Card from '../common/Card';
import SpeedIcon from '@mui/icons-material/Speed';
import ThunderstormIcon from '@mui/icons-material/Thunderstorm';
import ThermostatIcon from '@mui/icons-material/Thermostat';
import WifiIcon from '@mui/icons-material/Wifi';
import ErrorIcon from '@mui/icons-material/Error';
import CheckCircleIcon from '@mui/icons-material/CheckCircle';
import LightbulbIcon from '@mui/icons-material/Lightbulb';

// Mock data for mining devices
const mockMiners = [
  {
    id: 'miner-001',
    name: 'Antminer S19',
    status: 'online',
    temp: 65,
    hashrate: '95.2',
    efficiency: '34.5',
    powerDraw: '3250',
    uptime: '99.7%',
    location: 'Rack A, Unit 3',
    lastSeen: '2 mins ago',
    alerts: 0,
  },
  {
    id: 'miner-002',
    name: 'Antminer S19',
    status: 'online',
    temp: 68,
    hashrate: '94.8',
    efficiency: '33.9',
    powerDraw: '3270',
    uptime: '99.5%',
    location: 'Rack A, Unit 4',
    lastSeen: '1 min ago',
    alerts: 0,
  },
  {
    id: 'miner-003',
    name: 'Whatsminer M30S',
    status: 'warning',
    temp: 74,
    hashrate: '82.5',
    efficiency: '38.2',
    powerDraw: '3420',
    uptime: '97.2%',
    location: 'Rack B, Unit 1',
    lastSeen: '5 mins ago',
    alerts: 1,
  },
  {
    id: 'miner-004',
    name: 'Antminer S19',
    status: 'offline',
    temp: 0,
    hashrate: '0',
    efficiency: '0',
    powerDraw: '0',
    uptime: '85.3%',
    location: 'Rack B, Unit 2',
    lastSeen: '2 hrs ago',
    alerts: 2,
  },
  {
    id: 'miner-005',
    name: 'Whatsminer M30S',
    status: 'online',
    temp: 66,
    hashrate: '93.1',
    efficiency: '34.7',
    powerDraw: '3290',
    uptime: '99.8%',
    location: 'Rack B, Unit 3',
    lastSeen: '3 mins ago',
    alerts: 0,
  },
  {
    id: 'miner-006',
    name: 'Antminer S19 Pro',
    status: 'online',
    temp: 63,
    hashrate: '109.5',
    efficiency: '32.1',
    powerDraw: '3180',
    uptime: '99.9%',
    location: 'Rack C, Unit 1',
    lastSeen: '1 min ago',
    alerts: 0,
  },
  {
    id: 'miner-007',
    name: 'Antminer S19 Pro',
    status: 'online',
    temp: 64,
    hashrate: '108.7',
    efficiency: '32.4',
    powerDraw: '3200',
    uptime: '99.8%',
    location: 'Rack C, Unit 2',
    lastSeen: '2 mins ago',
    alerts: 0,
  },
  {
    id: 'miner-008',
    name: 'Antminer S19',
    status: 'warning',
    temp: 72,
    hashrate: '91.4',
    efficiency: '35.8',
    powerDraw: '3320',
    uptime: '98.5%',
    location: 'Rack C, Unit 3',
    lastSeen: '7 mins ago',
    alerts: 1,
  },
];

const DeviceCard = ({
  miner,
  onActivateLight,
}: {
  miner: any;
  onActivateLight: (id: string) => void;
}) => {
  const getStatusColor = (status: string) => {
    switch (status) {
      case 'online':
        return { bg: 'rgba(76, 175, 80, 0.1)', color: colors.success };
      case 'warning':
        return { bg: 'rgba(255, 152, 0, 0.1)', color: colors.warning };
      case 'offline':
        return { bg: 'rgba(244, 67, 54, 0.1)', color: colors.error };
      default:
        return { bg: 'rgba(97, 97, 97, 0.1)', color: colors.textSecondary };
    }
  };

  const statusColors = getStatusColor(miner.status);

  return (
    <Paper
      elevation={0}
      sx={{
        backgroundColor: colors.paper,
        borderRadius: 1,
        border: `1px solid ${colors.primary}20`,
        p: 2,
        position: 'relative',
        transition: 'transform 0.2s, box-shadow 0.2s',
        '&:hover': {
          transform: 'translateY(-3px)',
          boxShadow: `0 8px 16px -8px ${colors.shadow}`,
          borderColor: colors.primary,
        },
      }}
    >
      {/* Status indicator */}
      <Box
        sx={{
          position: 'absolute',
          top: 12,
          right: 12,
          width: 12,
          height: 12,
          borderRadius: '50%',
          backgroundColor: statusColors.color,
        }}
      />

      {/* Alert badge */}
      {miner.alerts > 0 && (
        <Chip
          icon={<ErrorIcon fontSize="small" />}
          label={miner.alerts}
          size="small"
          color="error"
          sx={{
            position: 'absolute',
            top: 10,
            right: 30,
            height: 20,
            fontSize: '0.75rem',
          }}
        />
      )}

      {/* Device name */}
      <Typography variant="h6" sx={{ mb: 1, fontWeight: 500 }}>
        {miner.name}
      </Typography>

      <Box sx={{ mb: 2 }}>
        <Typography
          variant="body2"
          color="textSecondary"
          sx={{ fontSize: '0.75rem' }}
        >
          {miner.location}
        </Typography>
        <Typography
          variant="body2"
          color="textSecondary"
          sx={{ fontSize: '0.75rem' }}
        >
          Last seen: {miner.lastSeen}
        </Typography>
      </Box>

      {/* Metrics */}
      <Box sx={{ display: 'flex', flexWrap: 'wrap', mb: 2, mx: -0.5 }}>
        <Box sx={{ width: '50%', p: 0.5 }}>
          <Box sx={{ display: 'flex', alignItems: 'center' }}>
            <SpeedIcon
              sx={{ fontSize: '1rem', color: colors.primary, mr: 0.5 }}
            />
            <Typography variant="body2" sx={{ fontSize: '0.8rem' }}>
              {miner.status !== 'offline' ? `${miner.hashrate} TH/s` : '—'}
            </Typography>
          </Box>
        </Box>
        <Box sx={{ width: '50%', p: 0.5 }}>
          <Box sx={{ display: 'flex', alignItems: 'center' }}>
            <ThermostatIcon
              sx={{ fontSize: '1rem', color: colors.primary, mr: 0.5 }}
            />
            <Typography variant="body2" sx={{ fontSize: '0.8rem' }}>
              {miner.status !== 'offline' ? `${miner.temp}°C` : '—'}
            </Typography>
          </Box>
        </Box>
        <Box sx={{ width: '50%', p: 0.5 }}>
          <Box sx={{ display: 'flex', alignItems: 'center' }}>
            <ThunderstormIcon
              sx={{ fontSize: '1rem', color: colors.primary, mr: 0.5 }}
            />
            <Typography variant="body2" sx={{ fontSize: '0.8rem' }}>
              {miner.status !== 'offline' ? `${miner.powerDraw}W` : '—'}
            </Typography>
          </Box>
        </Box>
        <Box sx={{ width: '50%', p: 0.5 }}>
          <Box sx={{ display: 'flex', alignItems: 'center' }}>
            <WifiIcon
              sx={{ fontSize: '1rem', color: colors.primary, mr: 0.5 }}
            />
            <Typography variant="body2" sx={{ fontSize: '0.8rem' }}>
              {miner.uptime}
            </Typography>
          </Box>
        </Box>
      </Box>

      {/* Actions */}
      <Box sx={{ display: 'flex', justifyContent: 'space-between' }}>
        <Button
          variant="outlined"
          size="small"
          sx={{
            fontSize: '0.75rem',
            textTransform: 'none',
            borderColor: colors.primary,
            color: colors.primary,
            '&:hover': {
              borderColor: colors.primary,
              backgroundColor: 'rgba(57, 134, 232, 0.08)',
            },
          }}
          onClick={() => console.log(`📊 Details for ${miner.id}`)}
        >
          Details
        </Button>
        <Tooltip title="Activate LED to locate this device">
          <Button
            variant="outlined"
            size="small"
            sx={{
              fontSize: '0.75rem',
              textTransform: 'none',
              borderColor: colors.primary,
              color: colors.primary,
              '&:hover': {
                borderColor: colors.primary,
                backgroundColor: 'rgba(57, 134, 232, 0.08)',
              },
            }}
            onClick={() => onActivateLight(miner.id)}
            startIcon={<LightbulbIcon fontSize="small" />}
          >
            Locate
          </Button>
        </Tooltip>
      </Box>
    </Paper>
  );
};

const MineInventoryDashboard = () => {
  const [activeLight, setActiveLight] = useState<string | null>(null);

  const handleActivateLight = (id: string) => {
    console.log(`💡 Activating light on device ${id}`);
    setActiveLight(id);

    // Auto-turn off after 5 seconds
    setTimeout(() => {
      setActiveLight(null);
      console.log(`💡 Light turned off on device ${id}`);
    }, 5000);
  };

  // Stats
  const totalMiners = mockMiners.length;
  const onlineMiners = mockMiners.filter((m) => m.status === 'online').length;
  const warningMiners = mockMiners.filter((m) => m.status === 'warning').length;
  const offlineMiners = mockMiners.filter((m) => m.status === 'offline').length;

  return (
    <Card
      title="Mine Inventory"
      subtitle="Status of all mining devices"
      accentColor={colors.cardAccentSuccess}
    >
      {/* Summary stats */}
      <Box sx={{ display: 'flex', flexWrap: 'wrap', gap: 2, mb: 3 }}>
        <Chip
          icon={<CheckCircleIcon />}
          label={`${onlineMiners} Online`}
          color="success"
          variant="outlined"
        />
        <Chip
          icon={<ErrorIcon />}
          label={`${warningMiners} Warning`}
          color="warning"
          variant="outlined"
        />
        <Chip
          icon={<ErrorIcon />}
          label={`${offlineMiners} Offline`}
          color="error"
          variant="outlined"
        />
        <Chip
          label={`${totalMiners} Total Devices`}
          variant="outlined"
          sx={{ borderColor: colors.primary, color: colors.primary }}
        />
      </Box>

      {/* Graphics layout */}
      <Box sx={{ display: 'flex', flexWrap: 'wrap', mx: -1 }}>
        {mockMiners.map((miner) => (
          <Box
            key={miner.id}
            sx={{
              width: {
                xs: '100%',
                sm: '50%',
                md: '33.33%',
                lg: '25%',
              },
              p: 1,
            }}
          >
            <DeviceCard miner={miner} onActivateLight={handleActivateLight} />
          </Box>
        ))}
      </Box>
    </Card>
  );
};

export default MineInventoryDashboard;
