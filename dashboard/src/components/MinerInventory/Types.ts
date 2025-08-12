export type MinerStatus = 'online' | 'warning' | 'offline';

export interface Miner {
  id: string;
  name: string;
  status: 'online' | 'warning' | 'offline';
  temp: number;
  hashrate: string;
  efficiency: string;
  powerDraw: string;
  maxPower: string;
  uptime: string;
  location: string;
  lastSeen: string;
  alerts: number;
  frequency: string;
  fanspeed: string;
  bestDiff: string;
  ASICModel: string;
  chipTemp: number;
  voltage: string;
  firmware: string;
  pools: string;
  mac: string;
  ismining: boolean;
}