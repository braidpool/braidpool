export enum Page {
  INSTALLATION = 'installation',
  DASHBOARD = 'dashboard',
  MINING_INVENTORY = 'mining-inventory',
  MEMPOOL = 'mempool',
  DAG_VISUALIZATION = 'dag-visualization',
  MINER_STATS = 'miner-stats',
  BITCOIN_STATS = 'bitcoin-stats',
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
  blocks: Block[];
}

export interface Block {
  id: string;
  height: number;
  version: number;
  timestamp: number;
  bits: number;
  nonce: number;
  difficulty: number;
  merkle_root: string;
  tx_count: number;
  size: number;
  weight: number;
  previousblockhash: string;
  mediantime: number;
  stale: boolean;
  extras: {
    reward: number;
    coinbaseRaw: string;
    orphans: any[];
    medianFee: number;
    feeRange: number[];
    totalFees: number;
    avgFee: number;
    avgFeeRate: number;
    utxoSetChange: number;
    avgTxSize: number;
    totalInputs: number;
    totalOutputs: number;
    totalOutputAmt: number;
    segwitTotalTxs: number;
    segwitTotalSize: number;
    segwitTotalWeight: number;
    virtualSize: number;
    coinbaseAddress: string;
    coinbaseAddresses: string[];
    coinbaseSignature: string;
    coinbaseSignatureAscii: string;
  };
}

export const miningPoolNames = [
  'Orange',
  'Blue',
  'Purple',
  'Yellow',
  'Green',
  'Red',
] as const;

export type MiningPool = (typeof miningPoolNames)[number];

export const miningPoolColors: Record<MiningPool, string> = {
  Orange: 'bg-orange-500',
  Blue: 'bg-blue-500',
  Purple: 'bg-purple-500',
  Yellow: 'bg-yellow-500',
  Green: 'bg-green-500',
  Red: 'bg-red-500',
};
