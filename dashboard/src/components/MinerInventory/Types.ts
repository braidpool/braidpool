import { Dispatch, SetStateAction } from 'react';
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
export type MinerAnalyticsPoint = {
  timestamp: number;
  hashrate: number;
  expected: number;
  efficiency: number;
  temperature: number;
  vrTemperature: number;
};
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
export interface MinerTableProps {
  miners: Miner[];
  minerHistory: Record<string, MinerAnalyticsPoint[]>;
  getAlerts: (miner: Miner) => MinerAlert[];
  expandedAlerts: Record<string, boolean>;
  setExpandedAlerts: Dispatch<SetStateAction<Record<string, boolean>>>;
  statusStyles: Record<Miner['status'], string>;
}
export interface MinerDashboardHeaderProps {
  totalMiners: number;
  totalHashrate: number;
  totalPower: number;
  avgEfficiency: number;
}
export interface MinerControlsProps {
  newMinerIP: string;
  setNewMinerIP: (ip: string) => void;
  addMinerByIP: () => void;
  loading: boolean;
  lastUpdate: Date | null;
}
