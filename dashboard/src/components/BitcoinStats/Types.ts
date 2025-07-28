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
  transactions: any[]; // will have to replace this with the final Transaction props
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
