//Beads
export interface Transaction {
  id: string;
  hash: string;
  timestamp: string;
  count: number;
  blockId: string;
  fee: number;
  size: number;
  feePaid: string;
  feeRate: number;
  inputs: number;
  outputs: number;
}
export interface TransactionListProps {
  transactions: Transaction[];
}

export interface Bead {
  id: string;
  name: string;
  timestamp: string;
  transactions: number;
  difficulty: number;
  parents: string[];
  details?: Transaction[];
  reward: number;
}

export interface BeadRowProps {
  bead: Bead;
  isExpanded: boolean;
  onToggle: (beadId: string) => void;
  isActive: boolean;
  transactions: Transaction[];
}

export interface BeadRewardTooltipProps {
  reward: number; // in BTC
  isOpen?: boolean;
}
//annimatedstats
export interface AnimatedStatCardProps {
  title: string;
  value: string;
  color?: string;
}

//Dashboard
export interface DashboardHeaderProps {
  activeTab: string;
  setActiveTab: (tab: string) => void;
}
//Latency
export interface LatencyData {
  chartData: {
    value: number;
    label: string;
    date: string;
    timestamp: number;
  }[];
  averageLatency: string;
  peakLatency: string;
  peerCount: number;
  validPings: number;
  timestamp: number;
}
export interface LatencyWebSocketMessage {
  type: 'latency_data';
  data: {
    pings: number[];
    averageLatency: number;
    peakLatency: number;
    peerCount: number;
    validPings: number;
    timestamp: string | number;
  };
}

export interface LatencyHistoryEntry {
  value: number;
  timestamp: number;
  date: string;
  label: string;
}

//Hashrate
export interface HashrateWebSocketMessage {
  type: 'hashrate_data';
  data: {
    hashrate: number;
    timestamp: string | number;
    networkDifficulty: number;
  };
}

export interface HashrateHistoryEntry {
  value: number;
  timestamp: number;
  date: string;
  label: string;
}

export interface HashrateData {
  history: { value: number; date: string; label: string; timestamp: number }[];
  current: string;
  peak: string;
  networkDifficulty: number;
}

//Transactions
export type TransactionDataItem = {
  value: number;
  label: string;
  date: Date;
  timestamp: number;
};

export type TransactionStats = {
  txRate: number;
  mempoolSize: number;
  avgFeeRate: number;
  avgTxSize: number;
  averagingWindow?: number;
};

export type TransactionTabProps = {
  chartHovered: boolean;
  setChartHovered: (val: boolean) => void;
  timeRange: string;
};

export interface BlockData {
  blockHash: string;
  timestamp: number;
  height: number;
  difficulty: number;
  txCount: number;
  reward: number;
  parent: string;
  transactions: any[];
}

export interface AdvancedchartProps {
  data: { value: number; timestamp: number }[];
  yLabel: string;
  unit: string;
  lineColor?: string;
}
//Reward section

export interface RewardHistoryChartProps {
  rewardHistory: { height: number; reward: number; label: string }[];
}

export interface RewardData {
  totalRewards: number;
  dailyAverage: number;
  weeklyProjection: number;
  monthlyProjection: number;
  lastReward: number;
  lastRewardTime: string;
  rewardHistory: { height: number; reward: number; label: string }[];
}

export interface RewardsData {
  blockCount: number;
  blockReward: number;
  totalRewards: number;
  rewardRate: number;
  lastRewardTime: number | null;
  halvings: number;
  nextHalving: number;
  blocksUntilHalving: number;
}
export type BeadId = string;
