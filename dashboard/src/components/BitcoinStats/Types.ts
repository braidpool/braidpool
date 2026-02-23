export interface PriceData {
  current: number;
  high24h: number;
  low24h: number;
  currencySymbol: string;
}

export interface GlobalStats {
  marketCap: string;
  marketCapChange: number;
  activeCryptocurrencies: number;
  activeMarkets: number;
  bitcoinDominance: number;
  lastUpdated: string;
}

export interface TransactionTableProps {
  transactions: BraidPoolTransaction[]; // will have to replace this with the final Transaction props
}

// All props will need to be updated here once RPC is ready, and will have to update <any> in tests and code later on
export interface TransactionInfo {
  txid: string;
  fee: number;
  vsize: number;
  value: number;
  rate: number;
  rbf: boolean;
  fullRbf?: boolean;
}

export interface RBFTransaction {
  tx: TransactionInfo;
  time: number;
  fullRbf?: boolean;
  replaces: RBFTransaction[];
}

export interface RBFTransactionRowProps {
  isReplacement?: boolean;
  tx: RBFTransaction;
  depth?: number;
  onSelect: (txid: string) => void;
  expandedTxs: Set<string>;
  toggleExpanded: (txid: string) => void;
}

// Transaction Types
export enum TransactionCategory {
  MEMPOOL = 'mempool',
  COMMITTED = 'committed',
  PROPOSED = 'proposed',
  SCHEDULED = 'scheduled',
  CONFIRMED = 'confirmed',
  REPLACED = 'replaced',
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
  confirmations: number;
  work?: number;
  workUnit?: string;
  vin: TransactionInput[];
  vout: TransactionOutput[];
  status: TransactionStatus;
  timestamp?: number;
  rbfSignaled?: boolean;
}

export const TRANSACTION_CATEGORY_LABELS: Record<TransactionCategory, string> =
  {
    [TransactionCategory.MEMPOOL]: 'Mempool',
    [TransactionCategory.COMMITTED]: 'Committed',
    [TransactionCategory.PROPOSED]: 'Proposed',
    [TransactionCategory.SCHEDULED]: 'Scheduled',
    [TransactionCategory.CONFIRMED]: 'Confirmed',
    [TransactionCategory.REPLACED]: 'Replaced',
  };

export const TRANSACTION_CATEGORY_DESCRIPTIONS: Record<
  TransactionCategory,
  string
> = {
  [TransactionCategory.MEMPOOL]: 'Transactions in bitcoind mempool only',
  [TransactionCategory.COMMITTED]: 'Transactions committed to cmempool node',
  [TransactionCategory.PROPOSED]: 'Transactions proposed for next block',
  [TransactionCategory.SCHEDULED]: 'Transactions scheduled for mining',
  [TransactionCategory.CONFIRMED]: 'Transactions confirmed in a block',
  [TransactionCategory.REPLACED]: 'Transactions replaced by RBF',
};
