export type MinerStatus = 'online' | 'warning' | 'offline';

export interface Miner {
  id: string;

  ASICModel: string;
  name: string;
  status: MinerStatus;
  temp: number;
  hashrate: string;
  efficiency: string;
  powerDraw: string;
  maxPower: number;
  uptime: string;
  location: string;
  lastSeen: string;
  alerts: number;
  frequency: number;
  fanspeed: string;
  bestDiff: number;
}
