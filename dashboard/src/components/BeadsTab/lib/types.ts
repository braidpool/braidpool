export interface Transaction {
  id: string;
  hash: string;
  timestamp: string;
  count: number;
  blockId: string;
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
