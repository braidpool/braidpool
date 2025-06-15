export interface PriceData {
  current: number;
  high24h: number;
  low24h: number;
  priceChange24h: number;
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
  transactions: any[];
}

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
