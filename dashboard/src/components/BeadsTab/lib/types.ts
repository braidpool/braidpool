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

export interface ChartDataPoint {
  value: number;
  label: string;
  date: Date;
  formattedDate?: string;
  trend?: 'up' | 'down' | 'neutral';
}

export interface TimeRange {
  label: string;
  value: string;
  days: number;
}

export interface Props {
  data: ChartDataPoint[];
  height?: number;
  isHovered?: boolean;
  showControls?: boolean;
  isLoading?: boolean;
  comparisonData?: ChartDataPoint[];
  comparisonLabel?: string;
  timeRange: string;
  primaryLabel?: string;
  tooltipFormatter?: (
    value: number,
    name: string,
    props?: any
  ) => [string | number, string | number];
}

export interface BeadRowProps {
  bead: Bead;
  isExpanded: boolean;
  onToggle: (beadId: string) => void;
  isActive: boolean;
  transactions: Transaction[];
  onParentClick: (parentHash: string) => void;
}

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

export interface AnimatedStatCardProps {
  title: string;
  value: string;
  color?: string;
}

export interface BeadRewardTooltipProps {
  reward: number; // in BTC
  isOpen?: boolean;
}

export interface TransactionListProps {
  transactions: Transaction[];
}

export interface LatencyTabProps {
  chartData: any[];
  isChartLoading: boolean;
  chartHovered: boolean;
  setChartHovered: (val: boolean) => void;
  timeRange: string;
}

export interface DashboardHeaderProps {
  activeTab: string;
  setActiveTab: (tab: string) => void;
}

export interface HashrateData {
  history: { value: number; date: string; label: string }[];
  current: string;
  peak: string;
  networkDifficulty: number;
  latency: number;
}

export interface LatencyData {
  chartData: { value: number; label: string; date: string }[];
  averageLatency: string;
  peakLatency: string;
  peerCount: number;
  validPings: number;
  timestamp: number;
}

export interface TransactionStats {
  mempoolSize: number;
  avgFeeRate: number;
  avgTxSize: number;
  txRate: number;
  totalFees: number;
}

export interface HistoryEntry {
  value: number;
  date: string;
  label: string;
  timestamp: number;
}

export interface LatencyEntry {
  value: number;
  label: string;
  date: string;
  timeStamp: string;
}

export interface ProcessedHashrateData {
  hashrate: number;
  timestamp: number;
  networkDifficulty: number;
  latency: number;
}

export interface ProcessedLatencyData {
  pings: number[];
  averageLatency: number;
  peakLatency: number;
  peerCount: number;
  validPings: number;
  timestamp: number;
}

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
export type ChartDataItem = {
  value: number;
  label: string;
  date: Date;
};

export type Stats = {
  txRate: number;
  mempoolSize: number;
  avgFeeRate: number;
  avgTxSize: number;
};

export type TransactionTabProps = {
  chartHovered: boolean;
  setChartHovered: (val: boolean) => void;
  timeRange: string;
};

type WebSocketMessage =
  | { type: 'block_data'; data: { txCount: number } }
  | { type: 'transaction_stats'; data: Stats };
