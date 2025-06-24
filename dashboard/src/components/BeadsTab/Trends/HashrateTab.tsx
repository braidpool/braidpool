import React, { useState, useEffect, useRef } from 'react';
import AdvancedChart from '../AdvancedChart';
import AnimatedStatCard from '../AnimatedStatCard';
import { HashrateData } from '../lib/types';
import { processHashrateData } from '../lib/utils/dataProcessor';

export default function HashrateTab({ timeRange }: { timeRange: string }) {
  const [hashrateData, setHashrateData] = useState<HashrateData>({
    history: [],
    current: '0 EH/s',
    peak: '0 EH/s',
    networkDifficulty: 0,
    latency: 0,
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
      console.error('[HashrateTab] WebSocket error:', error);
    };
    ws.onmessage = (event) => {
      try {
        const message = JSON.parse(event.data);
        if (message.type === 'hashrate_data') {
          const processed = processHashrateData(message.data);
          setHashrateData(processed);
          setIsLoading(false);
        }
      } catch (e) {
        setIsLoading(false);
        console.error('[HashrateTab] WebSocket message parse error:', e);
      }
    };
    return () => {
      if (ws.readyState === WebSocket.OPEN) {
        ws.close();
      }
    };
  }, [timeRange]);

  const chartData = (hashrateData.history || []).map((d: any) => ({
    value: parseFloat(d.value) || 0,
    date: new Date(d.date),
    label: new Date(d.date).toLocaleTimeString(),
  }));

  if (isLoading || !isConnected) {
    return (
      <div className="p-8 text-center text-red-900">
        Loading hashrate data...
      </div>
    );
  }

  return (
    <div className="space-y-6 bg-[#1c1c1c]">
      <div className="flex justify-between items-center">
        <div>
          <h3 className="text-xl font-bold text-blue-300">Pool Hashrate</h3>
          <p className="text-sm text-gray-400 mt-1">
            Live hashrate of the Braidpool
          </p>
        </div>
        <div className="bg-purple-900/30 px-3 py-1 rounded-md">
          <span className="text-purple-300 font-mono">
            {hashrateData.current}
          </span>
        </div>
      </div>

      <div className="relative border border-gray-800/50 rounded-xl p-6 h-auto bg-[#1c1c1c] backdrop-blur-md overflow-hidden">
        <AdvancedChart
          data={chartData}
          height={350}
          isLoading={isLoading}
          timeRange={timeRange}
          primaryLabel="Hashrate "
          tooltipFormatter={function (value, name): [string, string] {
            return [`${(value as number).toFixed(2)} Eh/s`, name as string];
          }}
        />
      </div>

      <div className="grid grid-cols-3 md:grid-cols-3 sm:grid-cols-1  gap-6">
        <AnimatedStatCard
          title="Current Hashrate"
          value={hashrateData.current}
        />
        <AnimatedStatCard
          title="Peak Hashrate (24h)"
          value={hashrateData.peak}
        />
        <AnimatedStatCard
          title="Network Difficulty"
          value={hashrateData.networkDifficulty.toExponential(2)}
        />
      </div>
    </div>
  );
}
