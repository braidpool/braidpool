import { useState, useEffect, useRef } from 'react';
import AdvancedChart from '../AdvancedChart';
import AnimatedStatCard from '../AnimatedStatCard';
import {
  TransactionTabProps,
  TransactionDataItem,
  TransactionStats,
} from '../lib/Types';
import { WEBSOCKET_URLS } from '../../../URLs';
import { MAX_HISTORY_LENGTH } from '../Constants';

export default function TransactionsTab({ timeRange }: TransactionTabProps) {
  const [chartData, setChartData] = useState<TransactionDataItem[]>([]);
  const [stats, setStats] = useState<TransactionStats>({
    txRate: 0,
    mempoolSize: 0,
    avgFeeRate: 0,
    avgTxSize: 0,
  });

  const [isLoading, setIsLoading] = useState<boolean>(true);
  const [isConnected, setIsConnected] = useState<boolean>(false);
  const [error, setError] = useState<string | null>(null);

  const wsRef = useRef<WebSocket | null>(null);

  useEffect(() => {
    const ws = new WebSocket(WEBSOCKET_URLS.MAIN_WEBSOCKET);
    let isMounted = true;
    wsRef.current = ws;

    ws.onopen = () => {
      if (!isMounted) return;
      setIsConnected(true);
      setIsLoading(false);
      setError(null);
    };

    ws.onerror = (error) => {
      setIsConnected(false);
      setIsLoading(false);
      setError('WebSocket connection error');
      console.error('[TransactionsTab] WebSocket error:', error);
    };

    ws.onmessage = (event) => {
      if (!isMounted) return;
      try {
        const parsed = JSON.parse(event.data);

        if (parsed.type === 'error') {
          setError(parsed.data?.message || 'Unknown error');
          return;
        }

        if (
          parsed.type === 'block_data' &&
          parsed.data?.txCount !== undefined
        ) {
          const now = new Date();
          const timeStamp = now.getTime();

          const newEntry: TransactionDataItem = {
            value: parsed.data.txCount,
            label: now.toLocaleTimeString('en-GB', {
              hour: '2-digit',
              minute: '2-digit',
              second: '2-digit',
            }),
            date: now,
            timestamp: timeStamp,
          };

          setChartData((prev) => {
            const lastEntry = prev[prev.length - 1];
            if (lastEntry && lastEntry.timestamp === timeStamp) return prev;

            const updated = [...prev, newEntry];
            if (updated.length > MAX_HISTORY_LENGTH) updated.shift();
            return updated;
          });
        }

        if (parsed.type === 'transaction_stats' && parsed.data) {
          setStats({
            txRate: parsed.data.txRate || 0,
            mempoolSize: parsed.data.mempoolSize || 0,
            avgFeeRate: parsed.data.avgFeeRate || 0,
            avgTxSize: parsed.data.avgTxSize || 0,
            averagingWindow: parsed.data.averagingWindow || 0,
          });
          setError(null);
        }
      } catch (e) {
        setIsLoading(false);
        setError('Failed to parse data');
        console.error('[TransactionsTab] WebSocket message parse error:', e);
      }
    };
    ws.onclose = () => {
      if (!isMounted) return;
      console.log('WebSocket disconnected');
      setIsConnected(false);
    };

    return () => {
      isMounted = false;
      ws.onopen = null;
      ws.onclose = null;
      ws.onerror = null;
      ws.onmessage = null;
      if (ws.readyState === WebSocket.OPEN) {
        ws.close();
      }
    };
  }, [timeRange]);

  const getCurrentRate = () => stats?.txRate || 0;
  const getRateLabel = () =>
    `Moving Avg (${stats?.averagingWindow || 0} blocks)`;

  return (
    <div className="space-y-4 ">
      <div className="flex justify-between items-center">
        <div>
          <h3 className="text-xl font-bold text-blue-300">
            Transaction Activity
          </h3>
          <p className="text-sm text-gray-400 mt-1">
            Real-time transaction statistics
          </p>
          {error && <p className="text-sm text-red-400 mt-1">Error: {error}</p>}
          {!isConnected && !error && (
            <p className="text-sm text-yellow-400 mt-1">Disconnected</p>
          )}
        </div>
        <div className="flex items-center gap-4">
          <div className="bg-purple-900/30 px-3 py-1 rounded-md">
            <div className="text-center">
              <span className="text-purple-300 font-mono text-lg">
                {getCurrentRate()
                  ? `${getCurrentRate().toFixed(1)} tx/min`
                  : isLoading
                    ? 'Loading...'
                    : 'No data'}
              </span>
              <div className="text-xs text-purple-400 mt-1">
                {getRateLabel()}
              </div>
            </div>
          </div>
        </div>
      </div>

      <div>
        <AdvancedChart
          data={chartData.slice(-10)}
          yLabel="Transactions per Block"
          unit="tx"
          lineColor="#8884d8"
        />
      </div>

      <div className="grid sm:grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6">
        <AnimatedStatCard
          title="Mempool Size"
          value={
            stats?.mempoolSize
              ? `${stats.mempoolSize.toLocaleString()} tx`
              : isLoading
                ? 'Loading...'
                : 'No data'
          }
        />
        <AnimatedStatCard
          title="Avg Fee Rate"
          value={
            stats?.avgFeeRate
              ? `${stats.avgFeeRate.toFixed(1)} sat/vB`
              : isLoading
                ? 'Loading...'
                : 'No data'
          }
        />
        <AnimatedStatCard
          title="Avg Tx Size"
          value={
            stats?.avgTxSize
              ? `${Math.round(stats.avgTxSize)} vB`
              : isLoading
                ? 'Loading...'
                : 'No data'
          }
        />
      </div>
    </div>
  );
}
