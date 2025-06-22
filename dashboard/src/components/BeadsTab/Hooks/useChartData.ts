import { useState, useEffect, useCallback } from 'react';
import { TIME_RANGES } from '../lib/constants';
import type {
  ChartDataPoint,
  HashrateData,
  LatencyData,
  TransactionStats,
} from '../lib/types';
import { useWebSocket } from './useWebSocket';

export function useChartData(timeRange: string) {
  const [data, setData] = useState<ChartDataPoint[]>([]);
  const [hashrateData, setHashrateData] = useState<HashrateData>({
    history: [],
    current: '0 EH/s',
    peak: '0 EH/s',
    networkDifficulty: 0,
    latency: 0,
  });
  const [latencyData, setLatencyData] = useState<LatencyData>({
    chartData: [],
    averageLatency: '0ms',
    peakLatency: '0ms',
    peerCount: 0,
    validPings: 0,
    timestamp: 0,
  });
  const [stats, setStats] = useState<TransactionStats>({
    mempoolSize: 0,
    avgFeeRate: 0,
    avgTxSize: 0,
    txRate: 0,
    totalFees: 0,
  });
  const [isLoading, setIsLoading] = useState(true);

  const selectedRange =
    TIME_RANGES.find((range) => range.value === timeRange) || TIME_RANGES[1];

  const handleMessage = useCallback(
    (message: any) => {
      setIsLoading(false);
      switch (message.type) {
        case 'Block_summary': {
          const now = new Date();
          const newDataPoint: ChartDataPoint = {
            value: message.data.txCount || 0,
            label: now.toLocaleTimeString('en-US', {
              hour: '2-digit',
              minute: '2-digit',
              second: '2-digit',
              hour12: true,
            }),
            date: now,
          };
          setData((prevData) =>
            [...prevData, newDataPoint].slice(-selectedRange.days * 24 * 60)
          ); // Keep data relevant to range
          break;
        }
        case 'transaction_stats':
          setStats(message.data);
          break;
        case 'hashrate_update':
          setHashrateData(message.data);
          break;
        case 'latency_update':
          setLatencyData(message.data);
          break;
        default:
          break;
      }
    },
    [selectedRange.days]
  );

  const handleError = useCallback((error: any) => {
    console.error('[ChartData] WebSocket error:', error);
    setIsLoading(false);
  }, []);

  const { isConnected } = useWebSocket({
    onMessage: handleMessage,
    onError: handleError,
  });

  useEffect(() => {
    setIsLoading(true);
    setData([]);
  }, [timeRange]);

  return {
    data,
    hashrateData,
    latencyData,
    stats,
    isLoading: isLoading || !isConnected,
  };
}
