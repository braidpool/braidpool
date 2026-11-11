import { ReactNode } from 'react';

export interface CardProps {
  title?: ReactNode;
  subtitle?: ReactNode;
  children: ReactNode;
  accentColor?: string;
  headerExtra?: ReactNode;
}

export type HeaderNavProps = {
  title?: string;
  currentPage: Page;
  setCurrentPage: (page: Page) => void;
};
export enum Page {
  DASHBOARD = 'dashboard',
  MINING_INVENTORY = 'mining-inventory',
  MEMPOOL = 'mempool',
  POOL_DOMINANCE = 'pool-dominance',
  BITCOIN_STATS = 'bitcoin-stats',
  NODE_HEALTH = 'node-health',
  DAG = 'dag',
  REWARDS = 'rewards',
  TRENDS = 'trends',
}
