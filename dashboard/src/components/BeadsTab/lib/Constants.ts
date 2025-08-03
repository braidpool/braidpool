import { Zap, Activity, Database,Cpu } from 'lucide-react';
import { PoolData } from './Types';
import { useState } from 'react';

export const TrendsTABS = [
  { id: 'hashrate', label: 'Hashrate', icon: Zap },
  { id: 'latency', label: 'Latency', icon: Activity },
  { id: 'transactions', label: 'Transactions', icon: Database },
  {id :'difficulty' , label:'Difficulty' , icon :Cpu},
];

export const TABS = [
  { id: 'beads', label: 'Bead Explorer' },
  { id: 'trends', label: 'Network Trends' },
  { id: 'rewards', label: 'Rewards' },
  {id: 'pool',label:'Pool Dominance'}
];
export const COLORS = [
    '#003A6B',
    '#1B5886',
    '#3776A1',
    ' #5293BB',
    '#6EB1D6',
    '#89CFF1',
    '#91A6FF',
  ];
 