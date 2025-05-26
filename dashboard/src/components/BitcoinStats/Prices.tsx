import React, { useState, useEffect } from 'react';
import Select from '@mui/material/Select';
import MenuItem from '@mui/material/MenuItem';
import InputLabel from '@mui/material/InputLabel';
import FormControl from '@mui/material/FormControl';
import Skeleton from '@mui/material/Skeleton';
import Alert from '@mui/material/Alert';
import Typography from '@mui/material/Typography';
import ArrowUpward from '@mui/icons-material/ArrowUpward';
import ArrowDownward from '@mui/icons-material/ArrowDownward';
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

interface PriceData {
  current: number;
  high24h: number;
  low24h: number;
  priceChange24h: number;
  currencySymbol: string;
}

interface GlobalStats {
  marketCap: string;
  marketCapChange: number;
  activeCryptocurrencies: number;
  activeMarkets: number;
  bitcoinDominance: number;
  lastUpdated: string;
}

const BitcoinPriceTracker: React.FC = () => {
  const [currency, setCurrency] = useState<'USD' | 'EUR' | 'GBP' | 'JPY'>(
    'USD'
  );
  const [priceData, setPriceData] = useState<PriceData | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [globalStats, setGlobalStats] = useState<GlobalStats | null>(null);
  const [priceDirection, setPriceDirection] = useState<'up' | 'down' | null>(
    null
  );
  const [isConnected, setIsConnected] = useState(false);
  const [priceHistory, setPriceHistory] = useState<
    { price: number; time: string }[]
  >([]);
  const MAX_HISTORY_ITEMS = 30; // Keep last 30 data points

  useEffect(() => {
    const websocket = new WebSocket('ws://localhost:5000');

    websocket.onopen = () => {
      console.log('Connected to WebSocket server');
      setIsConnected(true);
      setLoading(false);
    };

    websocket.onmessage = (event) => {
      try {
        const data = JSON.parse(event.data);
        console.log('Received data:', data);
        if (data.type === 'bitcoin_update') {
          const currentPrice = data.data.price?.[currency];
          const currencySymbol = getCurrencySymbol(currency);

          setPriceData((prev) => {
            const previousPrice = prev?.current ?? currentPrice;
            const priceChange =
              ((currentPrice - previousPrice) / previousPrice) * 100;
            if (previousPrice !== currentPrice) {
              setPriceDirection(currentPrice > previousPrice ? 'up' : 'down');
            }
            return {
              current: currentPrice,
              high24h: prev
                ? Math.max(prev.high24h, currentPrice)
                : currentPrice,
              low24h: prev ? Math.min(prev.low24h, currentPrice) : currentPrice,
              priceChange24h: isFinite(priceChange) ? priceChange : 0,
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
              lastUpdated: new Date(now).toLocaleString(),
            });
          }

          // Update price history
          setPriceHistory((prev) => {
            const newHistory = [
              ...prev,
              { price: currentPrice, time: timeString },
            ];
            // Keep only the last MAX_HISTORY_ITEMS entries
            return newHistory.slice(-MAX_HISTORY_ITEMS);
          });
        }
      } catch (err) {
        console.error('Error parsing WebSocket message:', err);
        setError('Invalid data format received');
      }
    };

    // websocket.onerror = (error) => {
    //   console.error('WebSocket error:', error);
    //   setError('Connection error');
    //   setLoading(false);
    // };

    websocket.onclose = () => {
      console.log('WebSocket disconnected');
      setIsConnected(false);
      setLoading(false);
    };

    return () => {
      websocket.close();
    };
  }, [currency]);

  const getCurrencySymbol = (curr: string) => {
    switch (curr) {
      case 'EUR':
        return '€';
      case 'GBP':
        return '£';
      case 'JPY':
        return '¥';
      default:
        return '$';
    }
  };

  const formatPrice = (value: number): string => {
    if (!value) return '--';
    return new Intl.NumberFormat('en-US', {
      style: 'decimal',
      minimumFractionDigits: 2,
      maximumFractionDigits: 2,
    }).format(value);
  };

  const formatLargeNumber = (value: number): string => {
    if (!value) return '--';
    if (value >= 1e12) return `${(value / 1e12).toFixed(2)}T`;
    if (value >= 1e9) return `${(value / 1e9).toFixed(2)}B`;
    if (value >= 1e6) return `${(value / 1e6).toFixed(2)}M`;
    return new Intl.NumberFormat('en-US').format(value);
  };

  // Show skeletons if:
  // 1. Still loading (initial state)
  // 2. Not connected to WebSocket yet
  // 3. No data received yet
  const showSkeletons = loading || !isConnected || (!priceData && !globalStats);

  return (
    <div className="p-4">
      <div className="w-full flex flex-wrap justify-center items-center gap-4 md:gap-20 p-4 md:p-6 rounded-lg shadow-sm mb-6">
        <FormControl size="small" className="min-w-[100px]">
          <InputLabel id="currency-select-label">Currency</InputLabel>
          {
            <Select
              labelId="currency-select-label"
              value={currency}
              label="Currency"
              onChange={(e) => setCurrency(e.target.value as typeof currency)}
            >
              <MenuItem value="USD">USD</MenuItem>
              <MenuItem value="EUR">EUR</MenuItem>
              <MenuItem value="GBP">GBP</MenuItem>
              <MenuItem value="JPY">JPY</MenuItem>
            </Select>
          }
        </FormControl>

        {error ? (
          <Alert severity="error" className="w-full">
            {error}
          </Alert>
        ) : showSkeletons ? (
          <div className="flex gap-6">
            {[...Array(3)].map((_, i) => (
              <div key={i} className="flex flex-col gap-1">
                <Skeleton variant="text" width={80} height={30} />
                <Skeleton variant="text" width={60} height={20} />
              </div>
            ))}
          </div>
        ) : priceData ? (
          <>
            <div className="flex flex-col">
              <div className="flex items-center gap-2">
                <Typography
                  variant="h6"
                  className={`font-bold ${priceDirection === 'up' ? 'text-green-500' : priceDirection === 'down' ? 'text-red-500' : ''}`}
                >
                  {priceData.currencySymbol}
                  {formatPrice(priceData.current)}
                </Typography>
                {priceDirection === 'up' && (
                  <ArrowUpward className="text-green-500" fontSize="small" />
                )}
                {priceDirection === 'down' && (
                  <ArrowDownward className="text-red-500" fontSize="small" />
                )}
              </div>
              <Typography variant="caption" className="text-gray-500">
                Current Price in {currency}
              </Typography>
            </div>

            <div className="flex flex-col">
              <Typography variant="body1">
                {priceData.currencySymbol}
                {formatPrice(priceData.high24h)}
              </Typography>
              <Typography variant="caption" className="text-gray-500">
                24H High
              </Typography>
            </div>

            <div className="flex flex-col">
              <Typography variant="body1">
                {priceData.currencySymbol}
                {formatPrice(priceData.low24h)}
              </Typography>
              <Typography variant="caption" className="text-gray-500">
                24H Low
              </Typography>
            </div>
          </>
        ) : null}
      </div>

      {showSkeletons ? (
        <div className="flex flex-wrap justify-center items-center gap-4 md:gap-20 p-4">
          {[...Array(5)].map((_, i) => (
            <div key={i} className="flex flex-col gap-1">
              <Skeleton variant="text" width={80} height={30} />
              <Skeleton variant="text" width={60} height={20} />
            </div>
          ))}
        </div>
      ) : globalStats ? (
        <div className="flex flex-wrap justify-center items-center gap-4 md:gap-20 p-4">
          <div className="flex flex-col">
            <Typography variant="body1">{globalStats.marketCap}</Typography>
            <Typography variant="caption" className="text-gray-500">
              Market Cap
            </Typography>
          </div>
          <div className="flex flex-col">
            <Typography variant="body1">
              {globalStats.activeCryptocurrencies}
            </Typography>
            <Typography variant="caption" className="text-gray-500">
              Active Cryptocurrencies
            </Typography>
          </div>

          <div className="flex flex-col">
            <Typography variant="body1">{globalStats.activeMarkets}</Typography>
            <Typography variant="caption" className="text-gray-500">
              Active Markets
            </Typography>
          </div>

          <div className="flex flex-col">
            <Typography variant="body1">
              {globalStats.bitcoinDominance.toFixed(2)}%
            </Typography>
            <Typography variant="caption" className="text-gray-500">
              BTC Dominance
            </Typography>
          </div>

          <div className="flex flex-col">
            <Typography variant="body1">{globalStats.lastUpdated}</Typography>
            <Typography variant="caption" className="text-gray-500">
              Last Updated
            </Typography>
          </div>
        </div>
      ) : null}

      <div className="w-full flex flex-wrap justify-center items-center gap-4 md:gap-20 p-4 md:p-6 rounded-lg mb-6">
        <div className="grid sm:grid-cols-1 md:grid-cols-2 gap-4 md:gap-20 p-4">
          {/* Graph 1: Bitcoin Dominance */}
          <div className="flex flex-col w-full h-72">
            <Typography variant="body1" className="font-semibold">
              Bitcoin 24H Price Range
            </Typography>
            <Typography variant="caption" className="text-gray-500 mb-2">
              Displays the low, current, and high prices of Bitcoin in the
              selected currency over the past 24 hours.
            </Typography>
            <ResponsiveContainer width="100%" height="100%">
              <BarChart
                data={[
                  { label: 'Low', value: priceData?.low24h ?? 0 },
                  { label: 'Current', value: priceData?.current ?? 0 },
                  { label: 'High', value: priceData?.high24h ?? 0 },
                ]}
              >
                <XAxis dataKey="label" />
                <YAxis />
                <Tooltip />
                <Legend />
                <Bar dataKey="value" fill="#8884d8" />
              </BarChart>
            </ResponsiveContainer>
          </div>
          {/* Graph 2: Bitcoin Price LineChart */}
          <div className="flex flex-col w-full h-72">
            <Typography variant="body1" className="font-semibold">
              Bitcoin Price History (Live)
            </Typography>
            <Typography variant="caption" className="text-gray-500 mb-2">
              Live updates of Bitcoin price in {currency}
            </Typography>
            <ResponsiveContainer width="100%" height="100%">
              <LineChart
                data={priceHistory}
                margin={{ top: 5, right: 20, bottom: 5, left: 45 }}
              >
                <CartesianGrid strokeDasharray="3 3" />
                <XAxis
                  dataKey="time"
                  tick={{ fontSize: 10 }}
                  interval={Math.floor(MAX_HISTORY_ITEMS / 5)} // Show fewer ticks
                />
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
                  isAnimationActive={false} // Disable animation for better performance with live data
                />
              </LineChart>
            </ResponsiveContainer>
          </div>
        </div>
      </div>

      <div className="w-full flex flex-wrap justify-center items-center gap-4 md:gap-20 p-4 md:p-6 rounded-lg mb-6">
        <div className="grid sm:grid-cols-1 md:grid-cols-2 gap-4 md:gap-20 p-4">
          {/* Graph 2: Fear-Greed Meter */}
          <div className="flex flex-col w-full h-72">
            <Typography variant="body1" className="font-semibold">
              Fear & Greed Index
            </Typography>
            <Typography variant="caption" className="text-gray-500 mb-2">
              The crypto market behaviour is very emotional. People tend to get
              greedy when the market is rising which results in FOMO (Fear of
              missing out). Also, people often sell their coins in irrational
              reaction of seeing red numbers. With our Fear and Greed Index, we
              try to save you from your own emotional overreactions.
            </Typography>
            <div className="w-full flex flex-wrap justify-center items-center">
              <ResponsiveContainer width="50%" height="100%">
                <img
                  className="bg-blend-multiply"
                  src="https://alternative.me/crypto/fear-and-greed-index.png"
                  alt="Latest Crypto Fear & Greed Index"
                />
              </ResponsiveContainer>
            </div>
          </div>
          {/* Graph 2: Bitcoin Price LineChart */}
          <div className="flex flex-col w-full h-72">
            <Typography variant="body1" className="font-semibold">
              Something
            </Typography>
            <Typography variant="caption" className="text-gray-500 mb-2">
              Something
            </Typography>
            <ResponsiveContainer width="100%" height="100%">
              <div>Something</div>
            </ResponsiveContainer>
          </div>
        </div>
      </div>
    </div>
  );
};

export default BitcoinPriceTracker;
