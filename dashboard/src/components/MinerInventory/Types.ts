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
