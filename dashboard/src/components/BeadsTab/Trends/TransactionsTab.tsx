import { useState, useEffect, useRef } from 'react';
import AdvancedChart from '../AdvancedChart';
import AnimatedStatCard from '../AnimatedStatCard';
import { TransactionTabProps, ChartDataItem, Stats } from '../lib/types';

const MAX_HISTORY_LENGTH = 50;

export default function TransactionsTab({ timeRange }: TransactionTabProps) {
  const [chartData, setChartData] = useState<ChartDataItem[]>([]);
  const [stats, setStats] = useState<Stats>({
    txRate: 0,
    mempoolSize: 0,
    avgFeeRate: 0,
    avgTxSize: 0,
  });

  const [isLoading, setIsLoading] = useState<boolean>(true);
  const [isConnected, setIsConnected] = useState<boolean>(false);

  const wsRef = useRef<WebSocket | null>(null);

  useEffect(() => {
    const ws = new WebSocket('ws://localhost:5000');
    wsRef.current = ws;

    ws.onopen = () => {
      setIsConnected(true);
      setIsLoading(false);
    };

    ws.onclose = () => setIsConnected(false);

    ws.onerror = (error) => {
      setIsConnected(false);
      setIsLoading(false);
      console.error('[TransactionsTab] WebSocket error:', error);
    };

    ws.onmessage = (event) => {
      try {
        const parsed = JSON.parse(event.data);

        if (
          parsed.type === 'block_data' &&
          parsed.data?.txCount !== undefined
        ) {
          const now = new Date();
          const timeStamp = now.getTime();

          const newEntry: ChartDataItem = {
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

        if (
          parsed.type === 'transaction_stats' &&
          parsed.data &&
          typeof parsed.data.txRate === 'number'
        ) {
          setStats(parsed.data);
        }
      } catch (e) {
        setIsLoading(false);
        console.error('[TransactionsTab] WebSocket message parse error:', e);
      }
    };

    return () => {
      if (ws.readyState === WebSocket.OPEN) {
        ws.close();
      }
    };
  }, [timeRange]);

  return (
    <div className="space-y-6 bg-[#1c1c1c]">
      <div className="flex justify-between items-center">
        <div>
          <h3 className="text-xl font-bold text-blue-300 ">
            Transaction Activity
          </h3>
          <p className="text-sm text-gray-400 mt-1">
            Real-time transaction statistics
          </p>
        </div>
        <div className="bg-purple-900/30 px-3 py-1 rounded-md">
          <span className="text-purple-300 font-mono">
            {stats?.txRate ? `${stats.txRate.toFixed(1)} tx/min` : 'Loading...'}
          </span>
        </div>
      </div>

      <div>
        <AdvancedChart
          data={chartData.slice(-10)}
          yLabel="Transaction"
          unit="tx/min"
          lineColor="#8884d8"
        />
      </div>

      <div className="grid sm:grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6">
        <AnimatedStatCard
          title="Mempool Size"
          value={stats?.mempoolSize ? `${stats.mempoolSize} tx` : 'Loading...'}
        />
        <AnimatedStatCard
          title="Avg Fee Rate"
          value={
            stats?.avgFeeRate
              ? `${stats.avgFeeRate.toFixed(1)} sats/vB`
              : 'Loading...'
          }
        />
        <AnimatedStatCard
          title="Avg Tx Size"
          value={stats?.avgTxSize ? `${stats.avgTxSize} vB` : 'Loading...'}
        />
      </div>
    </div>
  );
}
