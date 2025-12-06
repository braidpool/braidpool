export interface BraidPoolApiConfig {
  baseUrl: string;
  timeout: number;
  retries: number;
}

export interface ApiTransaction {
  txid: string;
  hash?: string;
  category?: string;
  size?: number;
  weight?: number;
  fee?: number;
  fee_rate?: number;
  inputs?: number;
  outputs?: number;
  confirmations: number;
  work?: string | number | null;
  work_unit?: string;
  timestamp?: number;
  rbf_signaled?: boolean;
  status?: {
    confirmed: boolean;
    block_height?: number;
    block_hash?: string;
    block_time?: number;
  };
  vin?: any[];
  vout?: any[];
}

export interface ApiMempoolInfo {
  count: number;
  vsize: number;
  total_fee: number;
  fee_histogram: Array<[number, number]>;
}
