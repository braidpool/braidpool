import React, { useState, useEffect, useRef } from 'react';
import {
  LineChart,
  Line,
  XAxis,
  YAxis,
  Tooltip,
  CartesianGrid,
  ResponsiveContainer,
} from 'recharts';
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

  const [isConnected, setIsConnected] = useState(false);
  const wsRef = useRef<WebSocket | null>(null);

  
  const [hashrateHistory, setHashrateHistory] = useState<any[]>([]);
  const peakHashrate = useRef(0);

  const processHashrateData = (data: any) => {
    const { hashrate, timestamp, networkDifficulty } = data;
    const time = new Date(timestamp).getTime();

    if (!hashrate || isNaN(hashrate)) return;

    const lastEntry = hashrateHistory.at(-1);
    if (lastEntry?.timestamp === time) return; // skip duplicate timestamps

    const historyEntry = {
      value: hashrate,
      timestamp: time,
      label: new Date(time).toLocaleTimeString(),
      date: new Date(time).toISOString(),
    };

    const updatedHistory = [...hashrateHistory, historyEntry].slice(
      -MAX_HISTORY_LENGTH
    );

    if (hashrate > peakHashrate.current) {
      peakHashrate.current = hashrate;
    }

    setHashrateHistory(updatedHistory);

    setHashrateData({
      history: updatedHistory,
      current: `${hashrate.toFixed(2)} EH/s`,
      peak: `${peakHashrate.current.toFixed(2)} EH/s`,
      networkDifficulty,
    });
  };

  useEffect(() => {
    setHashrateHistory([]);
    peakHashrate.current = 0;

    const ws = new WebSocket('ws://localhost:5000');
    wsRef.current = ws;

    ws.onopen = () => {
      setIsConnected(true);
    };
    ws.onclose = () => setIsConnected(false);
    ws.onerror = (error) => {
      setIsConnected(false);
      console.error('[HashrateTab] WebSocket error:', error);
    };
    ws.onmessage = (event) => {
      try {
        const message = JSON.parse(event.data);
        if (message.type === 'hashrate_data') {
          processHashrateData(message.data);
        }
      } catch (e) {
        console.error('[HashrateTab] WebSocket parse error:', e);
      }
    };

    return () => {
      if (ws.readyState === WebSocket.OPEN) ws.close();
    };
  }, [timeRange]);

  const chartData = (hashrateData.history || [])
    .map((d) => ({
      value: Number(d.value) || 0,
      timestamp: d.timestamp ? Number(d.timestamp) : undefined,
    }))
    .sort((a, b) => (a.timestamp || 0) - (b.timestamp || 0));

  if (!isConnected) {
    return (
      <div className="p-8 text-center text-red-500">
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

      <div className="relative border border-gray-800/50 rounded-xl p-6 bg-[#1c1c1c]">
        <ResponsiveContainer width="100%" height={350}>
          <LineChart data={chartData}>
            <CartesianGrid stroke="#4b5563" strokeDasharray="3 3" />
            <XAxis
              dataKey="timestamp"
              type="number"
              domain={['auto', 'auto']}
             tickFormatter={(ts) => new Date(ts).toLocaleTimeString()}
              stroke="#ccc"
              tick={{ fontSize: 12 }}
            />
            <YAxis
              stroke="#ccc"
              tick={{ fontSize: 12 }}
            />
            <Tooltip
              labelFormatter={(ts) => new Date(ts).toLocaleTimeString()}
              formatter={(value: number) => [
                `${value.toFixed(2)} EH/s`,
                'Hashrate',
              ]}
              contentStyle={{
                backgroundColor: '#1f2937',
                borderColor: '#3b82f6',
                borderRadius: 8,
              }}
              labelStyle={{ color: '#fff' }}
              itemStyle={{ color: '#fff' }}
            />
            <Line
              type="monotone"
              dataKey="value"
              stroke="#3b82f6"
              strokeWidth={2}
              dot={true}
            />
          </LineChart>
        </ResponsiveContainer>
      </div>

      <div className="grid sm:grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6">
        <AnimatedStatCard title="Current Hashrate" value={hashrateData.current} />
        <AnimatedStatCard title="Peak Hashrate (24h)" value={hashrateData.peak} />
        <AnimatedStatCard
          title="Network Difficulty"
          value={hashrateData.networkDifficulty.toExponential(2)}
        />
      </div>
    </div>
  );
}
