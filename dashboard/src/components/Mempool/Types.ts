export interface Fee {
  sats_per_vbyte: number;
  fee_btc: number;
  fee_usd: number;
}

export interface FeeEstimate {
  high_priority?: Fee;
  medium_priority?: Fee;
  standard_priority?: Fee;
  economy?: Fee;
}

export interface BlockFeeHistoryItem {
  time: string;
  btc: number;
  usd: number;
}

export interface MempoolData {
  mempool: {
    vsize: number;
    count: number;
    total_fee_btc: number;
    total_fee_usd: number;
  };
  fees: FeeEstimate;
  next_block_fees?: Fee;
  fee_distribution: Record<string, number>;
  block_fee_history?: BlockFeeHistoryItem[];
}

export interface FeeDistributionItem {
  name: string;
  value: number;
}
