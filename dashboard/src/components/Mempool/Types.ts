type MoneyValue = number | string | null;

export interface Fee {
  sats_per_vbyte: number;
  fee_btc: MoneyValue;
  fee_usd?: MoneyValue;
  fee_eur?: MoneyValue;
  fee_jpy?: MoneyValue;
  fee_gbp?: MoneyValue;
  fee_cad?: MoneyValue;
  fee_aud?: MoneyValue;
  fee_chf?: MoneyValue;
  fee_inr?: MoneyValue;
  fee_krw?: MoneyValue;
  fee_brl?: MoneyValue;
  fee_hkd?: MoneyValue;
  fee_sgd?: MoneyValue;
}

export interface BlockFeeHistoryItem {
  height: number;
  time: string;
  timestamp?: number;
  btc: MoneyValue;
  usd?: MoneyValue;
  eur?: MoneyValue;
  jpy?: MoneyValue;
  gbp?: MoneyValue;
  cad?: MoneyValue;
  aud?: MoneyValue;
  chf?: MoneyValue;
  inr?: MoneyValue;
  krw?: MoneyValue;
  brl?: MoneyValue;
  hkd?: MoneyValue;
  sgd?: MoneyValue;
}

export interface MempoolStats {
  count: number;
  vsize: number;
  total_fee_btc: MoneyValue;
  total_fee_usd?: MoneyValue;
  total_fee_eur?: MoneyValue;
  total_fee_jpy?: MoneyValue;
  total_fee_gbp?: MoneyValue;
  total_fee_cad?: MoneyValue;
  total_fee_aud?: MoneyValue;
  total_fee_chf?: MoneyValue;
  total_fee_inr?: MoneyValue;
  total_fee_krw?: MoneyValue;
  total_fee_brl?: MoneyValue;
  total_fee_hkd?: MoneyValue;
  total_fee_sgd?: MoneyValue;
}

export interface CurrencyRates {
  USD: number;
  EUR: number;
  JPY: number;
  GBP: number;
  CAD: number;
  AUD: number;
  CHF: number;
  INR: number;
  KRW: number;
  BRL: number;
  HKD: number;
  SGD: number;
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
