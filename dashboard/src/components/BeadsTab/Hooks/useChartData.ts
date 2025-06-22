import { useState, useEffect, useRef, useCallback } from 'react';
import { TIME_RANGES } from '../lib/constants';
import type { ChartDataPoint } from '../lib/types';
import { useWebSocket } from './useWebSocket';

export function useChartData(timeRange: string) {
  const [data, setData] = useState<ChartDataPoint[]>([]);
  const [isLoading, setIsLoading] = useState(true);
  const [dateRange, setDateRange] = useState({ start: '', end: '' });
  const [stats, setStats] = useState({
    mempoolSize: 0,
    avgFeeRate: 0,
    avgTxSize: 0,
    txRate: 0
  });

  const dataHistoryRef = useRef<ChartDataPoint[]>([]);

  const selectedRange = TIME_RANGES.find((range) => range.value === timeRange) || TIME_RANGES[1];

  const handleBlockData = useCallback((blockData: any) => {
    const now = new Date();
    const newDataPoint: ChartDataPoint = {
      value: blockData.txCount || 0,
      label: now.toLocaleTimeString('en-US', { 
        hour: '2-digit', 
        minute: '2-digit', 
        second: '2-digit',
        hour12: true 
      }),
      date: now,
      formattedDate: now.toLocaleDateString('en-US', {
        year: 'numeric',
        month: 'short',
        day: 'numeric',
        weekday: 'short',
      }),
      trend: 'neutral',
    };

    // Add to history
    dataHistoryRef.current.push(newDataPoint);

    // Keep only data within the selected time range
    const cutoffTime = new Date();
    cutoffTime.setDate(cutoffTime.getDate() - selectedRange.days);
    
    dataHistoryRef.current = dataHistoryRef.current.filter(
      point => point.date >= cutoffTime
    );

    

    setData([...dataHistoryRef.current]);
    setIsLoading(false);
  }, [selectedRange.days]);

  const handleTransactionStats = useCallback((statsData: any) => {
    setStats({
      mempoolSize: statsData.mempoolSize || 0,
      avgFeeRate: statsData.avgFeeRate || 0,
      avgTxSize: statsData.avgTxSize || 0,
      txRate: statsData.txRate || 0
    });
  }, []);

  const handleMessage = useCallback((message: any) => {
    if (message.type === 'Block_summary') {
      handleBlockData(message.data);
    } else if (message.type === 'transaction_stats') {
      handleTransactionStats(message.data);
    }
  }, [handleBlockData, handleTransactionStats]);

  const handleError = useCallback((error: any) => {
    console.error('[ChartData] WebSocket error:', error);
    setIsLoading(false);
  }, []);

  const { isConnected } = useWebSocket({
    onMessage: handleMessage,
    onError: handleError
  });

  useEffect(() => {
    setIsLoading(true);

    // Set date range for display
    const endDate = new Date();
    const startDate = new Date();
    startDate.setDate(endDate.getDate() - selectedRange.days);

    setDateRange({
      start: startDate.toLocaleDateString('en-US', {
        year: 'numeric',
        month: 'short',
        day: 'numeric',
      }),
      end: endDate.toLocaleDateString('en-US', {
        year: 'numeric',
        month: 'short',
        day: 'numeric',
      }),
    });
  }, [selectedRange.days]);

  return { data, isLoading: isLoading || !isConnected, dateRange, stats };
}
