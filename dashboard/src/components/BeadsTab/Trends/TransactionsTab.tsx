import { useState, useEffect, useRef } from 'react';
import AdvancedChart from '../AdvancedChart';
import AnimatedStatCard from '../AnimatedStatCard';

export default function TransactionsTab({
  chartHovered,
  setChartHovered,
  timeRange,
}: any) {
  const [chartData, setChartData] = useState<any[]>([]);
  const [stats, setStats] = useState<any>({});
  const [isLoading, setIsLoading] = useState(true);
  const [isConnected, setIsConnected] = useState(false);
  const wsRef = useRef<WebSocket | null>(null);

  useEffect(() => {
    const ws = new WebSocket('ws://localhost:5000');
    wsRef.current = ws;
    ws.onopen = () => {
      setIsConnected(true);
      setIsLoading(false);
    };
    ws.onclose = () => {
      setIsConnected(false);
    };
    ws.onerror = (error) => {
      setIsConnected(false);
      setIsLoading(false);
      console.error('[TransactionsTab] WebSocket error:', error);
    };
    ws.onmessage = (event) => {
      try {
        const message = JSON.parse(event.data);
        if (message.type === 'block_data') {
          const now = new Date();
          const newDataPoint = {
            value: message.data.txCount || 0,
            label: now.toLocaleTimeString('en-US', {
              hour: '2-digit',
              minute: '2-digit',
              second: '2-digit',
              hour12: true,
            }),
            date: now,
          };
          setChartData((prev) => [...prev, newDataPoint].slice(-100));
        } else if (message.type === 'transaction_stats') {
          setStats(message.data);
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
          <h3 className="text-xl font-bold text-blue-300">
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

      <div
        className="relative border border-gray-800/50 rounded-xl p-6 h-auto bg-[#1c1c1c] backdrop-blur-md overflow-hidden"
        onMouseEnter={() => setChartHovered(true)}
        onMouseLeave={() => setChartHovered(false)}
      >
        <AdvancedChart
          data={chartData}
          height={350}
          isHovered={chartHovered}
          isLoading={isLoading}
          timeRange={timeRange}
          primaryLabel="Transactions per Block"
        />
      </div>

      <div className="grid grid-cols-3 md:grid-cols-3 gap-6">
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
