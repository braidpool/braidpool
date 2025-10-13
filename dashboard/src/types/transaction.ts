export enum TransactionCategory {
  MEMPOOL = 'mempool',
  COMMITTED = 'committed',
  PROPOSED = 'proposed',
  SCHEDULED = 'scheduled',
  CONFIRMED = 'confirmed',
  REPLACED = 'replaced'
}

export interface TransactionInput {
  txid: string;
  vout: number;
  sequence: number;
  prevout?: {
    value: number;
  };
}

export interface TransactionOutput {
  value: number;
  scriptpubkey_type: string;
  scriptpubkey_address?: string;
}

export interface TransactionStatus {
  confirmed: boolean;
  block_height?: number;
  block_hash?: string;
  block_time?: number;
}

export interface BraidPoolTransaction {
  txid: string;
  hash: string;
  category: TransactionCategory;
  size: number;
  weight: number;
  fee: number;
  feeRate: number;
  inputs: number;
  outputs: number;
  confirmations?: number;
  work?: number;
  workUnit?: string;
  vin: TransactionInput[];
  vout: TransactionOutput[];
  status: TransactionStatus;
  timestamp?: number;
  rbfSignaled?: boolean;
}

export const TRANSACTION_CATEGORY_LABELS: Record<TransactionCategory, string> = {
  [TransactionCategory.MEMPOOL]: 'Mempool',
  [TransactionCategory.COMMITTED]: 'Committed',
  [TransactionCategory.PROPOSED]: 'Proposed',
  [TransactionCategory.SCHEDULED]: 'Scheduled',
  [TransactionCategory.CONFIRMED]: 'Confirmed',
  [TransactionCategory.REPLACED]: 'Replaced'
};

export const TRANSACTION_CATEGORY_DESCRIPTIONS: Record<TransactionCategory, string> = {
  [TransactionCategory.MEMPOOL]: 'Transactions in bitcoind mempool only',
  [TransactionCategory.COMMITTED]: 'Transactions committed to cmempool node',
  [TransactionCategory.PROPOSED]: 'Transactions proposed for next block',
  [TransactionCategory.SCHEDULED]: 'Transactions scheduled for mining',
  [TransactionCategory.CONFIRMED]: 'Transactions confirmed in a block',
  [TransactionCategory.REPLACED]: 'Transactions replaced by RBF'
};