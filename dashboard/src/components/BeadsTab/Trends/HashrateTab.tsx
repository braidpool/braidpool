import React, { useState, useEffect, useRef } from 'react';
import AdvancedChart from '../AdvancedChart';
import AnimatedStatCard from '../AnimatedStatCard';
import { HashrateData } from '../lib/types';

const MAX_HISTORY_LENGTH = 288;

export default function HashrateTab({ timeRange }: { timeRange: string }) {
  const [hashrateData, setHashrateData] = useState<HashrateData>({
    history: [],
    current: 'Loading',
    peak: 'Loading',
    networkDifficulty: 0,
   
  });

  const [isLoading, setIsLoading] = useState(true);
  const [isConnected, setIsConnected] = useState(false);
  const wsRef = useRef<WebSocket | null>(null);

  // Local state for handling history and peak
  const hashrateHistory = useRef<any[]>([]);
  const peakHashrate = useRef(0);

  const processHashrateData = (data: any) => {
    const { hashrate, timestamp, networkDifficulty } = data;
    const time = new Date(timestamp).getTime();

    const historyEntry = {
      value: hashrate,
      date: new Date(timestamp).toISOString(),
      label: new Date(timestamp).toLocaleTimeString(),
      timestamp: time,
    };

    const lastEntry = hashrateHistory.current[hashrateHistory.current.length - 1];

   
    if (lastEntry && lastEntry.timestamp === time) {
      return {
        ...hashrateData,
        history: [...hashrateHistory.current],
        current: `${hashrate.toFixed(2)} EH/s`,
        peak: `${peakHashrate.current.toFixed(2)} EH/s`,
        networkDifficulty,
        
      };
    }

    if (hashrateHistory.current.length >= MAX_HISTORY_LENGTH) {
      hashrateHistory.current.shift();
    }
    hashrateHistory.current.push(historyEntry);

    if (hashrate > peakHashrate.current) {
      peakHashrate.current = hashrate;
    }

    return {
      history: [...hashrateHistory.current],
      current: `${hashrate.toFixed(2)} EH/s`,
      peak: `${peakHashrate.current.toFixed(2)} EH/s`,
      networkDifficulty,
      
    };
  };

  useEffect(() => {
    hashrateHistory.current = [];
    peakHashrate.current = 0;

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
          primaryLabel="Hashrate"
          tooltipFormatter={(value, name) => {
            return [`${(value as number).toFixed(2)} EH/s`, name as string];
          }}
        />
      </div>

      <div className="grid sm:grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6">
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
