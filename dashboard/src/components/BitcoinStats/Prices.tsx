import React, { useState, useEffect } from 'react';
import {
  BarChart,
  Bar,
  XAxis,
  YAxis,
  Tooltip,
  Legend,
  ResponsiveContainer,
  LineChart,
  Line,
  CartesianGrid,
} from 'recharts';
import { GlobalStats, PriceData } from './Types';
import {
  formatLargeNumber,
  formatPrice,
  getCurrencySymbol,
  getLatestTransactions,
  latestRBFTransactions,
} from './Utils';
import TransactionTable from './TransactionTable';
import RBFTransactionTable from './RBFTransactionTable';
import { useRef } from 'react';
import { WEBSOCKET_URLS } from '../../URLs';
import { MAX_HISTORY_ITEMS } from './Constants';

const CURRENCIES = ['USD', 'EUR', 'GBP', 'JPY'] as const;

const BitcoinPriceTracker: React.FC = () => {
  const [currency, setCurrency] = useState<'USD' | 'EUR' | 'GBP' | 'JPY'>(
    'USD'
  );
  const [transactions, setTransactions] = useState<any[]>([]);
  const [rbftransactions, setrbfTransactions] = useState<any[]>([]);
  const [priceData, setPriceData] = useState<PriceData | null>(null);
  const [globalStats, setGlobalStats] = useState<GlobalStats | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [priceDirection, setPriceDirection] = useState<'up' | 'down' | null>(
    null
  );
  const [isConnected, setIsConnected] = useState(false);
  const [priceHistory, setPriceHistory] = useState<
    { price: number; time: string }[]
  >([]);
  const showSkeletons = loading || !isConnected || (!priceData && !globalStats);
  const currencyRef = useRef(currency);

  useEffect(() => {
    currencyRef.current = currency;
  }, [currency]);

  useEffect(() => {
    const fetchTransactions = async () => {
      const data = await getLatestTransactions();
      setTransactions(data as any[]);
    };

    fetchTransactions();

    const fetchRbfTransactions = async () => {
      const data = await latestRBFTransactions();
      setrbfTransactions(data as any[]);
    };

    fetchRbfTransactions();

    const intervalId = setInterval(() => {
      fetchTransactions();
      fetchRbfTransactions();
    }, 5000);

    return () => clearInterval(intervalId);
  }, []);

  useEffect(() => {
    const websocket = new WebSocket(WEBSOCKET_URLS.MAIN_WEBSOCKET);
    let isMounted = true;

    websocket.onopen = () => {
      if (!isMounted) return;
      setIsConnected(true);
      setLoading(false);
    };

    websocket.onmessage = (event) => {
      if (!isMounted) return;

      try {
        const data = JSON.parse(event.data);

        if (data.type === 'bitcoin_update') {
          const selectedCurrency = currencyRef.current;
          const currentPrice = data.data.price?.[selectedCurrency]?.current;
          const high24hPrice = data.data.price?.[selectedCurrency]?.high24h;
          const low24hPrice = data.data.price?.[selectedCurrency]?.low24h;
          const currencySymbol = getCurrencySymbol(selectedCurrency);

          setPriceData((prev) => {
            const previousPrice = prev?.current ?? currentPrice;

            if (previousPrice !== currentPrice) {
              setPriceDirection(currentPrice > previousPrice ? 'up' : 'down');
            }

            return {
              current: currentPrice,
              high24h: Math.max(high24hPrice, currentPrice),
              low24h: Math.min(low24hPrice, currentPrice),
              currencySymbol,
            };
          });

          const now = new Date();
          const timeString = now.toLocaleTimeString();

          if (data.data.global_stats) {
            setGlobalStats({
              marketCap: formatLargeNumber(data.data.global_stats.market_cap),
              marketCapChange: data.data.global_stats.market_cap_change,
              activeCryptocurrencies:
                data.data.global_stats.active_cryptocurrencies,
              activeMarkets: data.data.global_stats.active_markets,
              bitcoinDominance: data.data.global_stats.bitcoin_dominance * 100,
              lastUpdated: now.toLocaleString(),
            });
          }

          setPriceHistory((prev) => {
            if (typeof currentPrice === 'number' && !isNaN(currentPrice)) {
              const newHistory = [
                ...prev.slice(-MAX_HISTORY_ITEMS),
                { price: currentPrice, time: timeString },
              ];

              return newHistory.slice(-MAX_HISTORY_ITEMS);
            }

            return prev;
          });
        }
      } catch (err) {
        setError('Invalid data format received');
      }
    };

    websocket.onclose = () => {
      if (!isMounted) return;
      setIsConnected(false);
      setLoading(false);
    };

    return () => {
      isMounted = false;

      if (websocket.readyState === WebSocket.OPEN) {
        websocket.close();
      }
    };
  }, []);

  return (
    <div className="p-4 md:p-6 space-y-6">
      {/* Currency Selector */}
      <div className="rounded-2xl border border-gray-200 dark:border-gray-700 p-4 shadow-sm">
        <div className="flex flex-wrap items-center justify-between gap-4">
          <label className="text-sm font-medium text-gray-400">Currency</label>

          <select
            value={currency}
            onChange={(e) => {
              const newCurrency = e.target.value as typeof currency;
              setCurrency(newCurrency);
              setPriceData(null);
              setPriceHistory([]);
              setPriceDirection(null);
            }}
            className="px-4 py-2 rounded-xl border border-gray-300 bg-transparent text-sm"
          >
            <option value={currency} hidden disabled>
              {currency}
            </option>

            {CURRENCIES.filter((curr) => curr !== currency).map((curr) => (
              <option key={curr} value={curr} className="text-black">
                {curr}
              </option>
            ))}
          </select>
        </div>
      </div>

      {/* Price Display */}
      <div className="rounded-2xl border border-gray-200 dark:border-gray-700 p-6 shadow-sm">
        {error ? (
          <div className="text-red-500 text-sm">{error}</div>
        ) : showSkeletons ? (
          <div className="flex gap-6 flex-wrap">
            {[1, 2, 3].map((i) => (
              <div
                key={i}
                className="h-8 w-28 rounded bg-gray-200 animate-pulse"
              />
            ))}
          </div>
        ) : priceData ? (
          <div className="grid grid-cols-1 md:grid-cols-3 gap-6 text-center md:text-left">
            <div>
              <p
                className={`text-3xl font-bold ${
                  priceDirection === 'up'
                    ? 'text-green-500'
                    : priceDirection === 'down'
                      ? 'text-red-500'
                      : ''
                }`}
              >
                {priceData.currencySymbol}
                {formatPrice(priceData.current)}
              </p>
              <p className="text-sm text-gray-400 mt-1">Current Price</p>
            </div>

            <div>
              <p className="text-lg font-semibold">
                {priceData.currencySymbol}
                {formatPrice(priceData.low24h)}
              </p>
              <p className="text-sm text-gray-400 mt-1">24h Low</p>
            </div>

            <div>
              <p className="text-lg font-semibold">
                {priceData.currencySymbol}
                {formatPrice(priceData.high24h)}
              </p>
              <p className="text-sm text-gray-400 mt-1">24h High</p>
            </div>
          </div>
        ) : null}
      </div>

      {/* Global Stats */}
      {globalStats && (
        <div className="grid grid-cols-2 md:grid-cols-5 gap-4">
          {[
            ['Market Cap', globalStats.marketCap],
            ['Active Cryptocurrencies', globalStats.activeCryptocurrencies],
            ['Active Markets', globalStats.activeMarkets],
            ['BTC Dominance', `${globalStats.bitcoinDominance.toFixed(2)}%`],
            ['Updated', globalStats.lastUpdated],
          ].map(([label, value]) => (
            <div
              key={label}
              className="rounded-2xl border border-gray-200 dark:border-gray-700 p-4 shadow-sm"
            >
              <p className="text-xs text-gray-400 mb-1">{label}</p>
              <p className="text-sm font-medium">{value}</p>
            </div>
          ))}
        </div>
      )}

      {/* Charts */}
      <div className="grid grid-cols-1 xl:grid-cols-2 gap-6">
        <div className="rounded-2xl border border-gray-200 dark:border-gray-700 p-4 h-80 shadow-sm">
          <p className="font-semibold mb-4">Bitcoin Price Range (24h)</p>

          <ResponsiveContainer width="100%" height="100%">
            <BarChart
              data={[
                { label: '24h Low', value: priceData?.low24h ?? 0 },
                { label: 'Current', value: priceData?.current ?? 0 },
                { label: '24h High', value: priceData?.high24h ?? 0 },
              ]}
            >
              <XAxis dataKey="label" />
              <YAxis />
              <Tooltip />
              <Legend />
              <Bar dataKey="value" fill="#6366f1" radius={[6, 6, 0, 0]} />
            </BarChart>
          </ResponsiveContainer>
        </div>

        <div className="rounded-2xl border border-gray-200 dark:border-gray-700 p-4 h-80 shadow-sm">
          <p className="font-semibold mb-4">Bitcoin Price History</p>

          <ResponsiveContainer width="100%" height="100%">
            <LineChart data={priceHistory}>
              <CartesianGrid strokeDasharray="3 3" />
              <XAxis dataKey="time" />
              <YAxis />
              <Tooltip />
              <Line
                type="monotone"
                dataKey="price"
                stroke="#6366f1"
                dot={false}
                isAnimationActive={false}
              />
            </LineChart>
          </ResponsiveContainer>
        </div>
      </div>

      {/* Transactions */}
      <TransactionTable transactions={transactions} />
      <RBFTransactionTable transactions={rbftransactions} />
    </div>
  );
};

export default BitcoinPriceTracker;
