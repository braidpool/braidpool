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
  streak: number;
  nextMilestone: number;
  achievements: string[];
  rewardHistory: { height: number; reward: number; label: string }[];
}

export interface AnimatedStatCardProps {
  title: string;
  value: string;
  change: string;
  icon: React.ReactNode;
  delay?: number;
  color?: string;
}
export interface BeadRewardTooltipProps {
  reward: number; // in BTC
  isOpen?: boolean;
}
export interface TransactionListProps {
  transactions: Transaction[];
}
export type LatencyEntry = {
  value: number;
  label: string;
  date: Date;
};

export type LatencyPayload = {
  chartData: LatencyEntry[];
  averageLatency: string;
  peakLatency: string;
  peerCount: number;
};