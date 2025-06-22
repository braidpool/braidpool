import type { TimeRange } from './types';
import { Zap, Activity, Database } from 'lucide-react';
export const TIME_RANGES: TimeRange[] = [
  { label: 'Week', value: 'week', days: 7 },
  { label: 'Month', value: 'month', days: 30 },
  { label: 'Quarter', value: 'quarter', days: 90 },
  { label: 'Year', value: 'year', days: 365 },
];

export const TrendsTABS = [
  { id: 'hashrate', label: 'Hashrate', icon: Zap },
  { id: 'latency', label: 'Latency', icon: Activity },
  { id: 'transactions', label: 'Transactions', icon: Database },
];

export const TABS = [
  { id: 'beads', label: 'Bead Explorer' },
  { id: 'trends', label: 'Network Trends' },
  { id: 'rewards', label: 'Rewards' },
];
