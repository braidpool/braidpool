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
  const MAX_HISTORY_ITEMS = 10;
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
    const websocket = new WebSocket('ws://localhost:5000/');
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

  return (
    <div className="p-4">
      {/* Currency Selector */}
      <div className="flex flex-wrap justify-center items-center gap-4 md:gap-20 p-4 md:p-6 rounded-lg shadow-sm mb-6">
        <label className="block text-lg font-medium text-white mb-1">
          Currency
        </label>
        <select
          value={currency}
          onChange={(e) => {
            const newCurrency = e.target.value as typeof currency;
            setCurrency(newCurrency);
            setPriceData(null);
            setPriceHistory([]);
            setPriceDirection(null);
          }}
          className="block py-2 px-4 ml-5 border border-gray-300 rounded-md shadow-sm focus:outline-none focus:ring-indigo-500 focus:border-indigo-500 sm:text-sm"
        >
          <option className="bg-gray-500" value="USD">
            USD
          </option>
          <option className="bg-gray-500" value="EUR">
            EUR
          </option>
          <option className="bg-gray-500" value="GBP">
            GBP
          </option>
          <option className="bg-gray-500" value="JPY">
            JPY
          </option>
        </select>
      </div>

      {/* Price Display */}
      <div className="flex flex-wrap justify-center items-center gap-4 md:gap-20 p-4 md:p-6 rounded-lg shadow-sm mb-6">
        {error ? (
          <div className="w-full p-3 bg-red-100 text-red-700 rounded-md">
            {error}
          </div>
        ) : showSkeletons ? (
          <div className="flex gap-6" data-testid="animate-pulse">
            {[...Array(3)].map((_, i) => (
              <div key={i} className="flex flex-col gap-1">
                <div className="animate-pulse bg-gray-200 rounded h-7 w-20"></div>
                <div className="animate-pulse bg-gray-200 rounded h-5 w-16"></div>
              </div>
            ))}
          </div>
        ) : priceData ? (
          <>
            <div className="flex flex-row justify-center items-center gap-4">
              <div className="flex items-center gap-2">
                <h6
                  className={`font-bold text-lg ${priceDirection === 'up' ? 'text-green-500' : priceDirection === 'down' ? 'text-red-500' : ''}`}
                >
                  {priceData.currencySymbol}
                  {formatPrice(priceData.current)}
                </h6>
                {priceDirection === 'up' && (
                  <svg
                    xmlns="http://www.w3.org/2000/svg"
                    className="h-5 w-5 text-green-500"
                    viewBox="0 0 20 20"
                    fill="currentColor"
                  >
                    <path
                      fillRule="evenodd"
                      d="M14.707 12.707a1 1 0 01-1.414 0L10 9.414l-3.293 3.293a1 1 0 01-1.414-1.414l4-4a1 1 0 011.414 0l4 4a1 1 0 010 1.414z"
                      clipRule="evenodd"
                    />
                  </svg>
                )}
                {priceDirection === 'down' && (
                  <svg
                    xmlns="http://www.w3.org/2000/svg"
                    className="h-5 w-5 text-red-500"
                    viewBox="0 0 20 20"
                    fill="currentColor"
                  >
                    <path
                      fillRule="evenodd"
                      d="M5.293 7.293a1 1 0 011.414 0L10 10.586l3.293-3.293a1 1 0 111.414 1.414l-4 4a1 1 0 01-1.414 0l-4-4a1 1 0 010-1.414z"
                      clipRule="evenodd"
                    />
                  </svg>
                )}
              </div>
              <span className="text-sm text-gray-500">
                Current Price in {currency}
              </span>
            </div>
            {/* Display 24h Low */}
            <div className="flex flex-col">
              <p className="text-base">
                {priceData.currencySymbol}
                {formatPrice(priceData.low24h)}
              </p>
              <span className="text-sm text-gray-500">24h Low</span>
            </div>
            {/* Display 24h High */}
            <div className="flex flex-col">
              <p className="text-base">
                {priceData.currencySymbol}
                {formatPrice(priceData.high24h)}
              </p>
              <span className="text-sm text-gray-500">24h High</span>
            </div>
          </>
        ) : null}
      </div>

      {/* Global Stats */}
      {showSkeletons ? (
        <div className="flex flex-wrap shadow-sm justify-center items-center gap-4 md:gap-20 p-4">
          {[...Array(5)].map((_, i) => (
            <div key={i} className="flex flex-col gap-1">
              <div className="animate-pulse bg-gray-200 rounded h-6 w-20"></div>
              <div className="animate-pulse bg-gray-200 rounded h-4 w-16"></div>
            </div>
          ))}
        </div>
      ) : globalStats ? (
        <div className="flex flex-wrap shadow-sm justify-center items-center gap-4 md:gap-20 p-4">
          <div className="flex flex-col">
            <p className="text-base">{globalStats.marketCap}</p>
            <span className="text-sm text-gray-500">Market Cap</span>
          </div>

          <div className="flex flex-col">
            <p className="text-base">{globalStats.activeCryptocurrencies}</p>
            <span className="text-sm text-gray-500">
              Active Cryptocurrencies
            </span>
          </div>

          <div className="flex flex-col">
            <p className="text-base">{globalStats.activeMarkets}</p>
            <span className="text-sm text-gray-500">Active Markets</span>
          </div>

          <div className="flex flex-col">
            <p className="text-base">
              {globalStats.bitcoinDominance.toFixed(2)}%
            </p>
            <span className="text-sm text-gray-500">BTC Dominance</span>
          </div>

          <div className="flex flex-col">
            <p className="text-base">{globalStats.lastUpdated}</p>
            <span className="text-sm text-gray-500">Last Updated</span>
          </div>
        </div>
      ) : null}

      {/* Charts Section */}
      <div className="w-full flex flex-wrap justify-center items-center gap-4 md:gap-20 p-4 mt-4 md:p-6 rounded-lg mb-6">
        {/* Price Range Bar Chart */}
        <div className="flex flex-col w-full h-80">
          <p className="font-semibold text-base">Bitcoin Price Range (24h)</p>
          <span className="text-sm text-gray-500 mb-2">
            Displays the 24-hour low, current, and 24-hour high prices in{' '}
            {currency}
          </span>
          <ResponsiveContainer width="99%" height="100%">
            <BarChart
              data={[
                { label: '24h Low', value: priceData?.low24h ?? 0 },
                { label: 'Current', value: priceData?.current ?? 0 },
                { label: '24h High', value: priceData?.high24h ?? 0 },
              ]}
              margin={{ left: 40, right: 20, top: 20, bottom: 20 }}
            >
              <XAxis dataKey="label" />
              <YAxis
                width={80}
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
                }}
                formatter={(value) => [
                  `${getCurrencySymbol(currency)}${formatPrice(Number(value))}`,
                  'Price',
                ]}
              />
              <Legend />
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
      <div className="w-full flex flex-wrap justify-center items-center gap-4 md:gap-20 p-4 md:p-6 rounded-lg mb-6">
        <div className="grid sm:grid-cols-1 md:grid-cols-2 gap-4 md:gap-20 p-4">
          {/* Fear-Greed Meter */}
          <div className="flex flex-col w-full h-72">
            <p className="font-semibold text-base">Fear & Greed Index</p>
            <span className="text-sm text-gray-500 mb-2">
              Market sentiment indicator
            </span>
            <div className="w-full flex flex-wrap justify-center items-center">
              <ResponsiveContainer width="50%" height="100%">
                <img
                  src="https://alternative.me/crypto/fear-and-greed-index.png"
                  alt="Latest Crypto Fear & Greed Index"
                  className="w-full h-auto"
                />
              </ResponsiveContainer>
            </div>
          </div>

          {/* Placeholder */}
          <div className="flex flex-col w-full h-72">
            <p className="font-semibold text-base">Market Trends</p>
            <span className="text-sm text-gray-500 mb-2">Coming soon...</span>
            <div className="w-full h-full flex items-center justify-center border-2 border-dashed border-gray-300 rounded-lg">
              <p className="text-gray-500">Additional visualization</p>
            </div>
          </div>
        </div>
      </div>

      {/* Transactions Table */}
      <TransactionTable transactions={transactions} />
      {/* RBF Transactions Table */}
      <RBFTransactionTable transactions={rbftransactions} />
    </div>
  );
};

export default BitcoinPriceTracker;
