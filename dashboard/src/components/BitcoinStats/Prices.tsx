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
  const [rbfTransactions, setRbfTransactions] = useState<any[]>([]);
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
  const currencyRef = useRef(currency);

  const showSkeletons = loading || !isConnected || (!priceData && !globalStats);

  useEffect(() => {
    currencyRef.current = currency;
  }, [currency]);

  useEffect(() => {
    const fetch = async () => {
      setTransactions((await getLatestTransactions()) as any[]);
      setRbfTransactions((await latestRBFTransactions()) as any[]);
    };
    fetch();
    const id = setInterval(fetch, 5000);
    return () => clearInterval(id);
  }, []);

  useEffect(() => {
    const ws = new WebSocket(WEBSOCKET_URLS.MAIN_WEBSOCKET);
    let mounted = true;

    ws.onopen = () => {
      if (!mounted) return;
      setIsConnected(true);
      setLoading(false);
    };
    ws.onclose = () => {
      if (!mounted) return;
      setIsConnected(false);
      setLoading(false);
    };
    ws.onmessage = (event) => {
      if (!mounted) return;
      try {
        const data = JSON.parse(event.data);
        if (data.type !== 'bitcoin_update') return;
        const c = currencyRef.current;
        const current = data.data.price?.[c]?.current;
        const high24h = data.data.price?.[c]?.high24h;
        const low24h = data.data.price?.[c]?.low24h;

        setPriceData((prev) => {
          const prevPrice = prev?.current ?? current;
          if (prevPrice !== current)
            setPriceDirection(current > prevPrice ? 'up' : 'down');
          return {
            current,
            high24h: Math.max(high24h, current),
            low24h: Math.min(low24h, current),
            currencySymbol: getCurrencySymbol(c),
          };
        });

        if (data.data.global_stats) {
          const g = data.data.global_stats;
          setGlobalStats({
            marketCap: formatLargeNumber(g.market_cap),
            marketCapChange: g.market_cap_change,
            activeCryptocurrencies: g.active_cryptocurrencies,
            activeMarkets: g.active_markets,
            bitcoinDominance: g.bitcoin_dominance * 100,
            lastUpdated: new Date().toLocaleString(),
          });
        }

        const time = new Date().toLocaleTimeString();
        setPriceHistory((prev) => {
          if (typeof current !== 'number' || isNaN(current)) return prev;
          return [
            ...prev.slice(-(MAX_HISTORY_ITEMS - 1)),
            { price: current, time },
          ];
        });
      } catch {
        setError('Invalid data received');
      }
    };

    return () => {
      mounted = false;
      if (ws.readyState === WebSocket.OPEN) ws.close();
    };
  }, []);

  const sym = priceData?.currencySymbol ?? getCurrencySymbol(currency);

  return (
    <div className="p-4 w-full">
      {/* Top bar */}
      <div className="flex items-center justify-between mb-8">
        <div className="flex border border-gray-200 dark:border-gray-700 rounded-full p-1 gap-1">
          {CURRENCIES.map((c) => (
            <button
              key={c}
              onClick={() => {
                setCurrency(c);
                setPriceData(null);
                setPriceHistory([]);
                setPriceDirection(null);
              }}
              className={`px-4 py-1.5 rounded-full text-sm font-medium transition-all ${
                currency === c
                  ? 'bg-indigo-600 text-white'
                  : 'text-gray-500 dark:text-gray-400 hover:text-gray-800 dark:hover:text-gray-200'
              }`}
            >
              {c}
            </button>
          ))}
        </div>

        <div className="flex items-center gap-2">
          <span
            className={`w-1.5 h-1.5 rounded-full ${isConnected ? 'bg-emerald-500 animate-pulse' : 'bg-red-400'}`}
          />
          <span className="text-xs text-gray-400">
            {isConnected ? 'Live' : 'Disconnected'}
          </span>
        </div>
      </div>

      {/* Error */}
      {error && (
        <div className="mb-6 px-4 py-3 bg-red-50 dark:bg-red-950 text-red-600 dark:text-red-400 text-sm rounded-lg border border-red-100 dark:border-red-900">
          {error}
        </div>
      )}

      {/* Price Display */}
      <div className="mb-8">
        <p className="text-xs uppercase tracking-widest text-gray-400 mb-2">
          Bitcoin · {currency}
        </p>

        {showSkeletons ? (
          <div className="flex gap-8 flex-wrap">
            <div className="animate-pulse bg-gray-200 dark:bg-gray-700 rounded h-9 w-36" />
            <div className="animate-pulse bg-gray-200 dark:bg-gray-700 rounded h-6 w-20 self-end" />
            <div className="animate-pulse bg-gray-200 dark:bg-gray-700 rounded h-6 w-20 self-end" />
          </div>
        ) : priceData ? (
          <div className="flex items-end gap-8 flex-wrap">
            <div>
              <div
                className={`text-4xl font-medium tracking-tight ${
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
              <p className="text-xs text-gray-400 mt-1">Current price</p>
            </div>
            <div>
              <div className="text-base text-gray-700 dark:text-gray-300">
                {sym}
                {formatPrice(priceData.low24h)}
              </div>
              <p className="text-xs text-gray-400 mt-1">24h low</p>
            </div>
            <div>
              <div className="text-base text-gray-700 dark:text-gray-300">
                {sym}
                {formatPrice(priceData.high24h)}
              </div>
              <p className="text-xs text-gray-400 mt-1">24h high</p>
            </div>
          </div>
        ) : null}
      </div>

      <hr className="border-gray-100 dark:border-gray-800 mb-8" />

      {/* Global Stats */}
      {showSkeletons ? (
        <div className="grid grid-cols-2 sm:grid-cols-4 gap-4 mb-8">
          {[...Array(4)].map((_, i) => (
            <div
              key={i}
              className="border border-gray-200 dark:border-gray-700 rounded-xl p-4"
            >
              <div className="animate-pulse bg-gray-200 dark:bg-gray-700 rounded h-3 w-16 mb-2" />
              <div className="animate-pulse bg-gray-200 dark:bg-gray-700 rounded h-5 w-20" />
            </div>
          ))}
        </div>
      ) : globalStats ? (
        <div className="grid grid-cols-2 sm:grid-cols-4 gap-4 mb-8">
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
              className="border border-gray-200 dark:border-gray-700 rounded-xl p-4"
            >
              <p className="text-xs uppercase tracking-widest text-gray-400 mb-1">
                {label}
              </p>
              <p className="text-sm font-medium text-gray-800 dark:text-gray-200">
                {value}
              </p>
            </div>
          ))}
        </div>
      ) : null}

      <hr className="border-gray-100 dark:border-gray-800 mb-8" />

      {/* Price History Line Chart */}
      <div className="mb-8">
        <p className="text-xs uppercase tracking-widest text-gray-400 mb-1">
          Price history
        </p>
        <p className="text-xs text-gray-400 mb-4">Live · {currency}</p>
        <div className="h-48">
          <ResponsiveContainer width="100%" height="100%">
            <LineChart
              data={priceHistory}
              margin={{ left: 10, right: 10, top: 10, bottom: 0 }}
            >
              <CartesianGrid strokeDasharray="3 3" stroke="#e5e7eb" />
              <XAxis
                dataKey="time"
                tick={{ fontSize: 10, fill: '#9ca3af' }}
                tickLine={false}
                axisLine={false}
                interval="preserveStartEnd"
              />
              <YAxis
                domain={['auto', 'auto']}
                tick={{ fontSize: 10, fill: '#9ca3af' }}
                tickLine={false}
                axisLine={false}
                tickFormatter={(v) => `${sym}${formatPrice(v)}`}
                width={60}
              />
              <Tooltip
                contentStyle={{
                  background: 'var(--tooltip-bg, #fff)',
                  border: '1px solid #e5e7eb',
                  borderRadius: 8,
                  fontSize: 12,
                }}
                formatter={(v) => [`${sym}${formatPrice(Number(v))}`, 'Price']}
                labelFormatter={(l) => `Time: ${l}`}
              />
              <Line
                type="monotone"
                dataKey="price"
                stroke="#6366f1"
                strokeWidth={1.5}
                dot={false}
                isAnimationActive={false}
              />
            </LineChart>
          </ResponsiveContainer>
        </div>
      </div>

      <hr className="border-gray-100 dark:border-gray-800 mb-8" />

      {/* 24h Range Bar Chart */}
      <div className="mb-8">
        <p className="text-xs uppercase tracking-widest text-gray-400 mb-1">
          24h range
        </p>
        <p className="text-xs text-gray-400 mb-4">
          Low / current / high in {currency}
        </p>
        <div className="h-40">
          <ResponsiveContainer width="100%" height="100%">
            <BarChart
              data={[
                { label: '24h Low', value: priceData?.low24h ?? 0 },
                { label: 'Current', value: priceData?.current ?? 0 },
                { label: '24h High', value: priceData?.high24h ?? 0 },
              ]}
              margin={{ left: 10, right: 10, top: 10, bottom: 0 }}
            >
              <XAxis
                dataKey="label"
                tick={{ fontSize: 11, fill: '#9ca3af' }}
                tickLine={false}
                axisLine={false}
              />
              <YAxis
                tick={{ fontSize: 10, fill: '#9ca3af' }}
                tickLine={false}
                axisLine={false}
                tickFormatter={(v) => `${sym}${formatPrice(v)}`}
                width={60}
                domain={[
                  (min: number) =>
                    Math.floor(
                      min -
                        (priceData
                          ? (priceData.high24h - priceData.low24h) * 0.1
                          : 0)
                    ),
                  (max: number) =>
                    Math.ceil(
                      max +
                        (priceData
                          ? (priceData.high24h - priceData.low24h) * 0.1
                          : 0)
                    ),
                ]}
              />
              <Tooltip
                contentStyle={{
                  background: 'var(--tooltip-bg, #fff)',
                  border: '1px solid #e5e7eb',
                  borderRadius: 8,
                  fontSize: 12,
                }}
                formatter={(v) => [`${sym}${formatPrice(Number(v))}`, 'Price']}
              />
              <Bar dataKey="value" fill="#6366f1" radius={[4, 4, 0, 0]} />
            </BarChart>
          </ResponsiveContainer>
        </div>
      </div>

      <hr className="border-gray-100 dark:border-gray-800 mb-8" />

      {/* Additional Charts Section */}
      <div className="w-full grid grid-cols-1 md:grid-cols-2 gap-6 p-4 md:p-6 mb-6">
        {/* Fear-Greed Meter */}
        <div className="flex flex-col">
          <p className="font-semibold text-base">Fear & Greed Index</p>
          <span className="text-sm text-gray-500 mb-3">
            Market sentiment indicator
          </span>

          <div className="w-full aspect-[4/3] max-w-lg mx-auto border border-gray-700 rounded-lg flex items-center justify-center">
            <img
              src="https://alternative.me/crypto/fear-and-greed-index.png"
              alt="Latest Crypto Fear & Greed Index"
              className="w-full h-full object-contain p-4"
            />
          </div>
        </div>

        {/* Market Trends */}
        <div className="flex flex-col">
          <p className="font-semibold text-base">Market Trends</p>
          <span className="text-sm text-gray-500 mb-3">Coming soon...</span>

          <div className="w-full aspect-[4/3] max-w-lg mx-auto border-2 border-dashed border-gray-300 rounded-lg flex items-center justify-center">
            <p className="text-gray-500">Additional visualization</p>
          </div>
        </div>
      </div>

      <hr className="border-gray-100 dark:border-gray-800 mb-8" />

      {/* Transactions */}
      <div className="mb-8">
        <p className="text-xs uppercase tracking-widest text-gray-400 mb-4">
          Latest transactions
        </p>
        <TransactionTable transactions={transactions} />
      </div>

      <hr className="border-gray-100 dark:border-gray-800 mb-8" />

      <div>
        <p className="text-xs uppercase tracking-widest text-gray-400 mb-4">
          RBF transactions
        </p>
        <RBFTransactionTable transactions={rbfTransactions} />
      </div>
    </div>
  );
};

export default BitcoinPriceTracker;
