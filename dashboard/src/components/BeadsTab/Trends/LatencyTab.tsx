import React, { useState, useEffect, useRef } from 'react';
import AdvancedChart from '../AdvancedChart';
import AnimatedStatCard from '../AnimatedStatCard';
import { LatencyData } from '../lib/types';
import { processLatencyData } from '../lib/utils/dataProcessor';

export default function LatencyTab({ timeRange }: { timeRange: string }) {
  const [latencyData, setLatencyData] = useState<LatencyData>({
    chartData: [],
    averageLatency: '0ms',
    peakLatency: '0ms',
    peerCount: 0,
    validPings: 0,
    timestamp: 0,
  });
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
      console.error('[LatencyTab] WebSocket error:', error);
    };
    ws.onmessage = (event) => {
      try {
        const message = JSON.parse(event.data);
        if (message.type === 'latency_data') {
          const processed = processLatencyData(message.data);
          setLatencyData(processed);
          setIsLoading(false);
        }
      } catch (e) {
        setIsLoading(false);
        console.error('[LatencyTab] WebSocket message parse error:', e);
      }
    };

    return () => {
      if (ws.readyState === WebSocket.OPEN) {
        ws.close();
      }
    };
  }, [timeRange]);

  const chartData = (latencyData.chartData || []).map((d: any) => ({
    value: d.value,
    date: new Date(d.date),
    label: new Date(d.date).toLocaleTimeString('en-US', {
      hour: '2-digit',
      minute: '2-digit',
      second: '2-digit',
      hour12: true,
      fractionalSecondDigits: 3,
    }),
  }));

  if (isLoading || !isConnected) {
    return (
      <div className="p-8 text-center text-purple-300">
        Loading latency data...
      </div>
    );
  }

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

      <div className="relative border border-gray-800/50 rounded-xl p-6 h-auto bg-[#1c1c1c] backdrop-blur-md overflow-hidden">
        <AdvancedChart
          data={chartData}
          height={350}
          isLoading={isLoading}
          timeRange={timeRange}
          primaryLabel="Latency (ms)"
          tooltipFormatter={function (value, name): [string, string] {
            return [`${(value as number).toFixed(2)} ms`, name as string];
          }}
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
