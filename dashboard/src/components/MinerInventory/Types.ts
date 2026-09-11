export interface Miner {
  id: string;
  ip: string;
  hostname: string;
  mac: string;
  make: string;
  model: string;
  firmware: string;

  // Status
  status: 'online' | 'warning' | 'offline';
  is_mining: boolean;
  uptime: number;
  errors: any[];
  alerts: number;
  lastSeen: string;

  // Hashrate
  hashrate_current: number;
  hashrate_avg: number;
  expected_hashrate: number;

  // Temperature
  temperature: number;
  temperature_max: number;
  vr_temperature: number;

  // Power
  power_usage: number;
  power_limit: number;
  efficiency: number;
  voltage: number;

  // Hardware
  fan_speeds: number[];
  chip_count: number;

  // Pool
  primary_pool: string;
  pools: any[];
}
export type HistoryPoint = {
  timestamp: number;
  totalHashrate: number;
  expectedHashrate: number;
  efficiency: number;
  temperature: number;
  vrTemperature: number;
};

export type AnalyticsChartsProps = {
  fleetHistory: HistoryPoint[];
};
export type MinerAlert = {
  message: string;
};
export interface MinerDashboardHeaderProps {
  totalMiners: number;
  totalHashrate: number;
  totalPower: number;
  avgEfficiency: number;
}
export interface MinerControlsProps {
  loading: boolean;
  lastUpdate: Date | null;
  wsConnected: boolean;
}
export type MinerType = 'asic' | 'cpu';

export interface ShareStats {
  submitted: number;
  accepted: number;
  rejected: number;
  acceptanceRate: number;
  blocksFound: number;
}

export interface HashrateInfo {
  currentKhashS: number;
  totalHashes: number;
  threads: number;
}

export interface ConnectionInfo {
  status: 'disconnected' | 'connecting' | 'connected' | 'error';
  poolUrl: string;
  username: string;
  uptimeSeconds: number;
  difficulty: number;
}

export interface WorkerInfo {
  id: number;
  status: string;
}

export interface ShareRecord {
  timestamp: string;
  jobId: string;
  nonce: string;
  hash: string;
  isBlockCandidate: boolean;
  accepted: boolean | null;
}

export interface MiningStatsSnapshot {
  minerId: string;
  minerVersion: string;
  uptimeSeconds: number;
  hashrate: HashrateInfo;
  shares: ShareStats;
  connection: ConnectionInfo;
  workerThreads: WorkerInfo[];
  recentShares: ShareRecord[];
}

export interface CpuMiner {
  id: string;
  api_url: string;
  label: string | null;
  is_online: boolean;
  last_seen: string | null;
  stats: MiningStatsSnapshot | null;
  created_at: string;
  updated_at: string;
}

export interface UnifiedMiner {
  id: string;
  type: MinerType;
  name: string;
  status: 'online' | 'warning' | 'offline';
  hashrateTHs: number;
  sharesAccepted: number | null;
  sharesSubmitted: number | null;
  uptime: number;
  power: number | null;
  efficiency: number | null;
  lastSeen: string;
  raw: Miner | CpuMiner;
}
