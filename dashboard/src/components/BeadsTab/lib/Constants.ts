import { Zap, Activity, Database, Cpu } from 'lucide-react';

export const TrendsTABS = [
  { id: 'hashrate', label: 'Hashrate', icon: Zap },
  { id: 'latency', label: 'Latency', icon: Activity },
  { id: 'transactions', label: 'Transactions', icon: Database },
  { id: 'difficulty', label: 'Difficulty', icon: Cpu },
];

export const TABS = [{ id: 'pool', label: 'Pool Dominance' }];
