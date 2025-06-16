export enum Page {
  INSTALLATION = 'installation',
  DASHBOARD = 'dashboard',
  MINING_INVENTORY = 'mining-inventory',
  MEMPOOL = 'mempool',
  DAG_VISUALIZATION = 'dag-visualization',
  MINER_STATS = 'miner-stats',
  BITCOIN_STATS = 'bitcoin-stats',
  NODE_HEALTH = 'node-health',
}

export interface DashboardMetricsProps {
  loading?: boolean;
}

export interface PoolHashrateChartProps {
  height?: number;
  data?: Array<{ time: string; value: number }>;
  loading?: boolean;
}

export interface RecentBlocksTableProps {
  maxHeight?: number;
}
