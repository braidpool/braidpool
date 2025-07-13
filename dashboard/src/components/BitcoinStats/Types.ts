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
