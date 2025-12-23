export interface Fee {
  sats_per_vbyte: number;
  fee_btc: number;
  fee_usd: number;
  fee_eur: number;
  fee_jpy: number;
}

export interface BlockFeeHistoryItem {
  height: number;
  time: string;
  timestamp?: number;
  btc: number;
  usd: number;
  eur: number;
  jpy: number;
}

export interface MempoolStats {
  count: number;
  vsize: number;
  total_fee_btc: number;
  total_fee_usd: number;
  total_fee_eur: number;
  total_fee_jpy: number;
}

export interface CurrencyRates {
  USD: number;
  EUR: number;
  JPY: number;
}

export interface MempoolData {
  mempool: MempoolStats;
  next_block_fees: Fee;
  fees: {
    high_priority: Fee;
    medium_priority: Fee;
    standard_priority: Fee;
    economy: Fee;
    minimum: Fee;
  };
  currency_rates: CurrencyRates;
  fee_distribution: Record<string, number>;
  block_fee_history: BlockFeeHistoryItem[];
}

export interface FeeDistributionItem {
  name: string;
  value: number;
}
