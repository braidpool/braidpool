// Bead represents a node in the DAG
export interface Bead {
  id: string
  cohort: number
  isBlock: boolean
  isHighestWorkPath: boolean
  isPoolMined: boolean
  parents: string[]
  children: string[]
  x?: number
  y?: number
  previousX?: number
  previousY?: number
}

// BraidData represents the entire DAG structure
export interface BraidData {
  beads: Bead[]
}

// NetworkStatsData represents network statistics
export interface NetworkStatsData {
  activeNodes: number
  nodeChange: number
  transactions: number
  transactionChange: number
  poolHashrate: number
  hashrateChange: number
  blocksMined: number
  blocksChange: number
}

// TransactionMetricsData represents transaction performance metrics
export interface TransactionMetricsData {
  currentTransactionRate: number
  transactionRateHistory: { timestamp: string; value: number }[]
  currentConfirmationTime: number
  confirmationTimeHistory: { timestamp: string; value: number }[]
  averageFee: number
  feeDistribution: { category: string; count: number }[]
}

// LogEntry represents a single log entry
export interface LogEntry {
  timestamp: Date
  message: string
  type: "info" | "success" | "error"
}

