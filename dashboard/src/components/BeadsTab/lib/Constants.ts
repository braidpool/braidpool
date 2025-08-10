import { Zap, Activity, Database, Cpu } from 'lucide-react';

export const TrendsTABS = [
  { id: 'hashrate', label: 'Hashrate', icon: Zap },
  { id: 'latency', label: 'Latency', icon: Activity },
  { id: 'transactions', label: 'Transactions', icon: Database },
  { id: 'difficulty', label: 'Difficulty', icon: Cpu },
];

export const TABS = [
  { id: 'beads', label: 'Bead Explorer' },
  { id: 'trends', label: 'Network Trends' },
  { id: 'rewards', label: 'Rewards' },
  { id: 'pool', label: 'Pool Dominance' },
];
