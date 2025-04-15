export interface Transaction {
    id: string
    hash: string
    timestamp: string
    count: number
    blockId: string
  }
  
  export interface Miner {
    id: string
    name: string
    timestamp: string
    transactions: number
    details?: Transaction[]
  }
  
  export interface ChartDataPoint {
    value: number
    label: string
    date: Date
    formattedDate?: string
    trend?: "up" | "down" | "neutral"
  }
  
  export interface TimeRange {
    label: string
    value: string
    days: number
  }