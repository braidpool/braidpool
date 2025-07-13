export type MinerStatus = 'online' | 'warning' | 'offline';

export interface Miner {
  id: string;
  name: string;
  status: MinerStatus;
  temp: number;
  hashrate: string;
  efficiency: string;
  powerDraw: string;
  uptime: string;
  location: string;
  lastSeen: string;
  alerts: number;
}