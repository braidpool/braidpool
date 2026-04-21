import React, { useState, useEffect, useRef } from 'react';
import {
  BarChart,
  Bar,
  XAxis,
  YAxis,
  Tooltip,
  ResponsiveContainer,
  LineChart,
  Line,
  CartesianGrid,
  Legend,
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
import { WEBSOCKET_URLS } from '../../URLs';
import { MAX_HISTORY_ITEMS } from './Constants';

const CURRENCIES = ['USD', 'EUR', 'GBP', 'JPY'] as const;
type Currency = (typeof CURRENCIES)[number];

const BitcoinPriceTracker: React.FC = () => {
  const [currency, setCurrency] = useState<Currency>('USD');
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

    const fetchRbfTransactions = async () => {
      const data = await latestRBFTransactions();
      setrbfTransactions(data as any[]);
    };

    fetchTransactions();
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
      console.log('Connected to WebSocket server');
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
        console.error('Error parsing WebSocket message:', err);
        setError('Invalid data format received');
      }
    };

    websocket.onclose = () => {
      if (!isMounted) return;
      console.log('WebSocket disconnected');
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

  const sym = priceData?.currencySymbol ?? getCurrencySymbol(currency);

  return (
    <div className="w-full p-4">
      {/* Top bar */}
      <div className="mb-6 flex flex-col items-center gap-3">
        <div className="flex gap-1 rounded-full border border-gray-200 p-1 dark:border-gray-700">
          {CURRENCIES.map((c) => (
            <button
              key={c}
              onClick={() => {
                setCurrency(c);
                setPriceData(null);
                setPriceHistory([]);
                setPriceDirection(null);
              }}
              className={`rounded-full px-4 py-1.5 text-sm font-medium transition-all ${
                currency === c
                  ? 'bg-indigo-600 text-white'
                  : 'text-gray-500 hover:text-gray-800 dark:text-gray-400 dark:hover:text-gray-200'
              }`}
            >
              {c}
            </button>
          ))}
        </div>
      </div>

      {/* Error */}
      {error && (
        <div className="mb-5 rounded-lg border border-red-100 bg-red-50 px-4 py-3 text-sm text-red-600 dark:border-red-900 dark:bg-red-950 dark:text-red-400">
          {error}
        </div>
      )}

      {/* Price Display */}

      <div className="mb-6 text-center">
        <p className="mb-2 text-xs uppercase tracking-widest text-gray-400">
          Bitcoin · {currency}
        </p>

        {showSkeletons ? (
          <div className="flex flex-wrap justify-center gap-6">
            <div className="h-7 w-28 animate-pulse rounded bg-gray-200 dark:bg-gray-700" />
            <div className="h-7 w-24 animate-pulse rounded bg-gray-200 dark:bg-gray-700" />
            <div className="h-7 w-24 animate-pulse rounded bg-gray-200 dark:bg-gray-700" />
          </div>
        ) : priceData ? (
          <div className="flex flex-wrap items-end justify-center gap-6">
            <div>
              <div
                className={`text-2xl font-medium ${
                  priceDirection === 'up'
                    ? 'text-emerald-500'
                    : priceDirection === 'down'
                      ? 'text-red-500'
                      : 'text-gray-900 dark:text-gray-100'
                }`}
              >
                {sym}
                {formatPrice(priceData.current)}
                <span className="ml-1 text-2xl">
                  {priceDirection === 'up'
                    ? '↑'
                    : priceDirection === 'down'
                      ? '↓'
                      : ''}
                </span>
              </div>
              <p className="mt-1 text-xs text-gray-400">Current price</p>
            </div>
            <div>
              <div className="text-2xl font-medium text-gray-700 dark:text-gray-300">
                {sym}
                {formatPrice(priceData.low24h)}
              </div>
              <p className="mt-1 text-xs text-gray-400">24h low</p>
            </div>
            <div>
              <div className="text-2xl font-medium text-gray-700 dark:text-gray-300">
                {sym}
                {formatPrice(priceData.high24h)}
              </div>
              <p className="mt-1 text-xs text-gray-400">24h high</p>
            </div>
          </div>
        ) : null}
      </div>
      {/* Global Stats */}
      {showSkeletons ? (
        <div className="mb-6 grid grid-cols-2 gap-4 sm:grid-cols-4">
          {[...Array(4)].map((_, i) => (
            <div
              key={i}
              className="rounded-xl border border-gray-200 p-4 dark:border-gray-700"
            >
              <div className="mb-2 h-3 w-16 animate-pulse rounded bg-gray-200 dark:bg-gray-700" />
              <div className="h-5 w-20 animate-pulse rounded bg-gray-200 dark:bg-gray-700" />
            </div>
          ))}
        </div>
      ) : globalStats ? (
        <div className="mb-6 grid grid-cols-2 gap-4 sm:grid-cols-4">
          {[
            { label: 'Market cap', value: globalStats.marketCap },
            {
              label: 'BTC dominance',
              value: `${globalStats.bitcoinDominance.toFixed(2)}%`,
            },
            {
              label: 'Active cryptos',
              value: globalStats.activeCryptocurrencies,
            },
            { label: 'Active markets', value: globalStats.activeMarkets },
          ].map(({ label, value }) => (
            <div
              key={label}
              className="rounded-xl border border-gray-200 p-4 dark:border-gray-700"
            >
              <p className="mb-1 text-xs uppercase tracking-widest text-gray-400">
                {label}
              </p>
              <p className="text-sm font-medium text-gray-800 dark:text-gray-200">
                {value}
              </p>
            </div>
          ))}
        </div>
      ) : null}

      <div className="w-full flex flex-wrap justify-center items-center gap-4 md:gap-20 p-4 mt-4 md:p-6 rounded-lg mb-6">
        {/* Price Range Bar Chart */}
        <div className="flex flex-col w-full h-80 -mx-6 sm:mx-0 px-6 sm:px-0">
          <p className="font-semibold text-base">Bitcoin Price Range (24h)</p>
          <span className="text-sm text-gray-500 mb-2">
            Displays the 24-hour low, current, and 24-hour high prices in{' '}
            {currency}
          </span>
          <ResponsiveContainer width="100%" height="100%">
            <BarChart
              data={[
                { label: '24h Low', value: priceData?.low24h ?? 0 },
                { label: 'Current', value: priceData?.current ?? 0 },
                { label: '24h High', value: priceData?.high24h ?? 0 },
              ]}
              margin={{
                left: -5,
                right: -5,
                top: 20,
                bottom: 20,
              }}
            >
              <XAxis dataKey="label" tick={{ fontSize: 12 }} />
              <YAxis
                width={50}
                tick={{ fontSize: 10 }}
                domain={[
                  (dataMin: number) =>
                    Math.floor(
                      dataMin -
                        (priceData
                          ? (priceData.high24h - priceData.low24h) * 0.1
                          : 0)
                    ),
                  (dataMax: number) =>
                    Math.ceil(
                      dataMax +
                        (priceData
                          ? (priceData.high24h - priceData.low24h) * 0.1
                          : 0)
                    ),
                ]}
                tickFormatter={(value) =>
                  `${getCurrencySymbol(currency)}${formatPrice(value)}`
                }
              />
              <Tooltip
                contentStyle={{
                  backgroundColor: 'black',
                  border: '1px solid #ccc',
                  fontSize: '12px',
                }}
                formatter={(value) => [
                  `${getCurrencySymbol(currency)}${formatPrice(Number(value))}`,
                  'Price',
                ]}
              />
              <Legend wrapperStyle={{ fontSize: '12px' }} />
              <Bar dataKey="value" fill="#8884d8" />
            </BarChart>
          </ResponsiveContainer>
        </div>

        {/* Price History Line Chart */}
        <div className="flex flex-col w-full h-80">
          <p className="font-semibold text-base">
            Bitcoin Price History (Live)
          </p>
          <span className="text-sm text-gray-500 mb-2">
            Live updates in {currency}
          </span>
          <ResponsiveContainer width="99%" height="100%">
            <LineChart
              data={priceHistory}
              margin={{ left: 60, right: 40, top: 20, bottom: 20 }}
            >
              <CartesianGrid strokeDasharray="3 3" />
              <XAxis dataKey="time" tick={{ fontSize: 10 }} interval={0} />
              <YAxis
                domain={['auto', 'auto']}
                tickFormatter={(value) =>
                  `${getCurrencySymbol(currency)}${formatPrice(value)}`
                }
              />
              <Tooltip
                contentStyle={{
                  backgroundColor: 'black',
                  border: '1px solid #ccc',
                }}
                formatter={(value) => [
                  `${getCurrencySymbol(currency)}${formatPrice(Number(value))}`,
                  'Price',
                ]}
                labelFormatter={(label) => `Time: ${label}`}
              />
              <Line
                type="monotone"
                dataKey="price"
                stroke="#8884d8"
                dot={false}
                isAnimationActive={false}
              />
            </LineChart>
          </ResponsiveContainer>
        </div>
      </div>
      {/* Additional Charts Section */}
      <div className="mb-5 grid w-full grid-cols-1 gap-4 p-0 md:grid-cols-2">
        <div className="flex flex-col">
          <p className="text-base font-semibold">Fear & Greed Index</p>
          <span className="mb-3 text-sm text-gray-500">
            Market sentiment indicator
          </span>

          <div className="flex w-full aspect-[5/3] max-w-lg items-center justify-center rounded-lg border border-gray-700 mx-auto">
            <img
              src="https://alternative.me/crypto/fear-and-greed-index.png"
              alt="Latest Crypto Fear & Greed Index"
              className="h-full w-full object-contain p-3"
            />
          </div>
        </div>

        <div className="flex flex-col">
          <p className="text-base font-semibold">Market Trends</p>
          <span className="mb-3 text-sm text-gray-500">Coming soon...</span>

          <div className="flex w-full aspect-[5/3] max-w-lg items-center justify-center rounded-lg border-2 border-dashed border-gray-300 mx-auto">
            <p className="text-gray-500">Additional visualization</p>
          </div>
        </div>
      </div>

      {/* Transactions */}
      <div className="mb-3">
        <p className="mb-2 text-xs uppercase tracking-widest text-gray-400">
          Latest transactions
        </p>
        <TransactionTable transactions={transactions} />
      </div>

      <div className="mt-2">
        <p className="mb-2 text-xs uppercase tracking-widest text-gray-400">
          RBF transactions
        </p>
        <RBFTransactionTable transactions={rbftransactions} />
      </div>
    </div>
  );
};

export default BitcoinPriceTracker;
