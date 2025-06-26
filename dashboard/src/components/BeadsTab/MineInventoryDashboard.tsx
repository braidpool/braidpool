import { useState } from 'react';
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
        return colors.success;
      case 'warning':
        return colors.warning;
      case 'offline':
        return colors.error;
      default:
        return colors.textSecondary;
    }
  };

  const statusColor = getStatusColor(miner.status);

  return (
    <div
      className="p-4 rounded-lg relative transition-all duration-200 hover:-translate-y-1 hover:shadow-lg border"
      style={{
        backgroundColor: colors.paper,
        borderColor: `${colors.primary}20`,
        boxShadow:
          '0 8px 16px -8px ' +
          (miner.status === 'online' ? colors.shadow : 'transparent'),
      }}
    >
      {/* Status indicator */}
      <div
        className="absolute top-3 right-3 w-3 h-3 rounded-full"
        style={{ backgroundColor: statusColor }}
      />

      {/* Alert badge */}
      {miner.alerts > 0 && (
        <div
          className="absolute top-2 right-12 flex items-center gap-1 px-2 py-0.5 rounded-full text-xs"
          style={{ backgroundColor: colors.error + '20', color: colors.error }}
        >
          <ErrorIcon className="text-sm" />
          {miner.alerts}
        </div>
      )}
      <br />

      {/* Device name */}
      <h3
        className="text-lg font-medium mb-2"
        style={{ color: colors.textPrimary }}
      >
        {miner.name}
      </h3>

      <div className="mb-4">
        <p className="text-xs" style={{ color: colors.textSecondary }}>
          {miner.location}
        </p>
        <p className="text-xs" style={{ color: colors.textSecondary }}>
          Last seen: {miner.lastSeen}
        </p>
      </div>

      {/* Metrics */}
      <div className="grid grid-cols-2 gap-2 mb-4">
        <div className="flex items-center gap-1">
          <SpeedIcon className="text-sm" style={{ color: colors.primary }} />
          <span className="text-sm">
            {miner.status !== 'offline' ? `${miner.hashrate} TH/s` : '—'}
          </span>
        </div>
        <div className="flex items-center gap-1">
          <ThermostatIcon
            className="text-sm"
            style={{ color: colors.primary }}
          />
          <span className="text-sm">
            {miner.status !== 'offline' ? `${miner.temp}°C` : '—'}
          </span>
        </div>
        <div className="flex items-center gap-1">
          <ThunderstormIcon
            className="text-sm"
            style={{ color: colors.primary }}
          />
          <span className="text-sm">
            {miner.status !== 'offline' ? `${miner.powerDraw}W` : '—'}
          </span>
        </div>
        <div className="flex items-center gap-1">
          <WifiIcon className="text-sm" style={{ color: colors.primary }} />
          <span className="text-sm">{miner.uptime}</span>
        </div>
      </div>

      {/* Actions */}
      <div className="flex justify-between">
        <button
          className="text-xs px-3 py-1 rounded border hover:bg-opacity-20 transition-colors"
          style={{
            borderColor: colors.primary,
            color: colors.primary,
            backgroundColor: 'transparent',
          }}
          onClick={() => console.log(`📊 Details for ${miner.id}`)}
        >
          Details
        </button>
        <button
          className="text-xs px-3 py-1 rounded border hover:bg-opacity-20 transition-colors flex items-center gap-1"
          style={{
            borderColor: colors.primary,
            color: colors.primary,
            backgroundColor: 'transparent',
          }}
          onClick={() => onActivateLight(miner.id)}
        >
          <LightbulbIcon className="text-sm" />
          Locate
        </button>
      </div>
    </div>
  );
};

const MineInventoryDashboard = () => {
  const [activeLight, setActiveLight] = useState<string | null>(null);
  const handleActivateLight = (id: string) => {
    /*...*/
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
      <div className="flex flex-wrap gap-2 mb-6">
        <div
          className="flex items-center gap-1 px-3 py-1 rounded-full border text-sm"
          style={{ borderColor: colors.success, color: colors.success }}
        >
          <CheckCircleIcon className="text-sm" />
          {onlineMiners} Online
        </div>
        <div
          className="flex items-center gap-1 px-3 py-1 rounded-full border text-sm"
          style={{ borderColor: colors.warning, color: colors.warning }}
        >
          <ErrorIcon className="text-sm" />
          {warningMiners} Warning
        </div>
        <div
          className="flex items-center gap-1 px-3 py-1 rounded-full border text-sm"
          style={{ borderColor: colors.error, color: colors.error }}
        >
          <ErrorIcon className="text-sm" />
          {offlineMiners} Offline
        </div>
        <div
          className="flex items-center gap-1 px-3 py-1 rounded-full border text-sm"
          style={{ borderColor: colors.primary, color: colors.primary }}
        >
          {totalMiners} Total Devices
        </div>
      </div>

      {/* Graphics layout */}
      <div className="grid lg:grid-cols-4 gap-4">
        {mockMiners.map((miner) => (
          <DeviceCard
            key={miner.id}
            miner={miner}
            onActivateLight={handleActivateLight}
          />
        ))}
      </div>
    </Card>
  );
};

export default MineInventoryDashboard;
