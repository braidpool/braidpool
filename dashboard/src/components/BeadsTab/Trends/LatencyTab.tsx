import React, { useState, useEffect, useRef } from 'react';
import AdvancedChart from '../AdvancedChart';
import AnimatedStatCard from '../AnimatedStatCard';
import {
  LatencyData,
  LatencyWebSocketMessage,
  LatencyHistoryEntry,
} from '../lib/Types';
import { WEBSOCKET_URLS } from '../../../URLs';
import { MAX_LATENCY_HISTORY } from '../Constants';

export default function LatencyTab({ timeRange }: { timeRange: string }) {
  const [latencyData, setLatencyData] = useState<LatencyData>({
    chartData: [],
    averageLatency: 'Loading',
    peakLatency: 'Loading',
    peerCount: 0,
    validPings: 0,
    timestamp: 0,
  });

  const [isLoading, setIsLoading] = useState(true);
  const [isConnected, setIsConnected] = useState(false);
  const wsRef = useRef<WebSocket | null>(null);

  const latencyHistory = useRef<LatencyHistoryEntry[]>([]);

  // ✅ Process incoming data
  const processLatencyData = (
    data: LatencyWebSocketMessage['data']
  ): LatencyData => {
    const { averageLatency, peakLatency, peerCount, validPings, timestamp } =
      data;

    const time = new Date(timestamp).getTime();

    const newEntry: LatencyHistoryEntry = {
      value: averageLatency,
      label: new Date(timestamp).toLocaleTimeString(),
      date: new Date(timestamp).toISOString(),
      timestamp: time,
    };

    const lastEntry = latencyHistory.current[latencyHistory.current.length - 1];

    if (lastEntry && lastEntry.timestamp === time) {
      return {
        ...latencyData,
        chartData: [...latencyHistory.current],
        averageLatency: `${averageLatency.toFixed(0)}ms`,
        peakLatency: `${peakLatency}ms`,
        peerCount,
        validPings,
        timestamp: time,
      };
    }

    if (latencyHistory.current.length >= MAX_LATENCY_HISTORY) {
      latencyHistory.current.shift();
    }

    latencyHistory.current.push(newEntry);

    return {
      chartData: [...latencyHistory.current],
      averageLatency: `${averageLatency.toFixed(0)}ms`,
      peakLatency: `${peakLatency}ms`,
      peerCount,
      validPings,
      timestamp: time,
    };
  };

  // ✅ WebSocket connection
  useEffect(() => {
    latencyHistory.current = [];

    const ws = new WebSocket(WEBSOCKET_URLS.MAIN_WEBSOCKET);
    let isMounted = true;
    wsRef.current = ws;

    ws.onopen = () => {
      if (!isMounted) return;
      setIsConnected(true);
      setIsLoading(false);
    };

    ws.onerror = (error) => {
      console.error('[LatencyTab] WebSocket error:', error);
      setIsConnected(false);
      setIsLoading(false);
    };

    ws.onmessage = (event) => {
      if (!isMounted) return;
      try {
        const message: LatencyWebSocketMessage = JSON.parse(event.data);
        if (message.type === 'latency_data') {
          const processed = processLatencyData(message.data);
          setLatencyData(processed);
          setIsLoading(false);
        }
      } catch (e) {
        console.error('[LatencyTab] WebSocket message parse error:', e);
        setIsLoading(false);
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

  // ✅ Chart data extraction
  const chartData = latencyData.chartData.slice(-10).map((d) => ({
    value: d.value,
    timestamp: d.timestamp,
  }));

  // ✅ Loading UI
  if (isLoading || !isConnected) {
    return (
      <div className="p-8 text-center text-purple-300">
        Loading latency data...
      </div>
    );
  }

  // ✅ Render UI
  return (
    <div className="space-y-6 bg-[#1c1c1c]">
      <div className="flex justify-between items-center">
        <div>
          <h3 className="text-xl font-bold text-blue-300">Network Latency</h3>
          <p className="text-sm text-gray-400 mt-1">
            Real-time latency measurements from peer nodes
          </p>
        </div>
        <div className="bg-purple-900/30 px-3 py-1 rounded-md">
          <span className="text-purple-300 font-mono">
            Avg: {latencyData.averageLatency} | {latencyData.validPings}/
            {latencyData.peerCount} peers
          </span>
        </div>
      </div>

      <div>
        <AdvancedChart
          data={chartData}
          yLabel="Latency"
          unit="ms"
          lineColor="#8884d8"
        />
      </div>

      <div className="grid sm:grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6">
        <AnimatedStatCard
          title="Average Latency"
          value={latencyData.averageLatency}
        />
        <AnimatedStatCard
          title="Peak Latency"
          value={latencyData.peakLatency}
        />
        <AnimatedStatCard
          title="Active Peers"
          value={`${latencyData.validPings}/${latencyData.peerCount}`}
        />
      </div>
    </div>
  );
}
