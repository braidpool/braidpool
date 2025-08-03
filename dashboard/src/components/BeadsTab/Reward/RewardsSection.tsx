import React, { useEffect, useRef, useState } from 'react';
import { LineChart, Line, XAxis, YAxis, Tooltip, Legend, ResponsiveContainer, CartesianGrid } from 'recharts';
import { calculateRewardAnalytics,formatValue } from '../lib/Utils';
import { RewardPoint } from '../lib/Types';

export  function RewardsDashboard() {
  const [rewardHistory, setRewardHistory] = useState<RewardPoint[]>([]);
  const wsRef = useRef<WebSocket | null>(null);

  useEffect(() => {
    const ws = new WebSocket('ws://localhost:5000');
    wsRef.current = ws;

    ws.onopen = () => {
      console.log('WebSocket connected');
    };

    ws.onmessage = (event) => {
      try {
        const message = JSON.parse(event.data);
        if (message.type === 'reward_update') {
          let rawData = message.data;

          if (Array.isArray(rawData)) {
            const parsedData = rawData.map((d: any) => ({
              height: Number(d.height),
              timestamp: d.timestamp,
              rewardBTC: Number(d.rewardBTC),
              rewardUSD: Number(d.rewardUSD),
            }));

            console.log("Parsed reward data:", parsedData);
            setRewardHistory(parsedData);
          } else {
            console.error('Expected array but got:', typeof rawData, rawData);
          }
        }
        console.log("Rewards received:", event.data);
      } catch (err) {
        console.error("WebSocket JSON error:", err);
      }
    };

    ws.onerror = (error) => {
      console.error('WebSocket error:', error);
    };

    ws.onclose = () => {
      console.log('WebSocket disconnected');
    };

    return () => {
      if (wsRef.current && wsRef.current.readyState === WebSocket.OPEN) {
        wsRef.current.close();
      }
    };
  }, []);

  const analytics = calculateRewardAnalytics(rewardHistory);

  const StatCard = ({ title, btcValue, usdValue, blocks, timeframe }: {
    title: string;
    btcValue: number;
    usdValue: number;
    blocks?: number;
    timeframe?: string;
  }) => (
    <div className=" p-4 rounded-lg border border-gray-600">
      <h3 className="text-gray-300 text-sm font-medium mb-2">{title}</h3>
      <div className="space-y-1">
        <div className="text-white text-lg font-semibold">
          {formatValue(btcValue, 'BTC')} BTC
        </div>
        <div className="text-white text-lg font-semibold">
          ${formatValue(usdValue, 'USD')}
        </div>
        {blocks !== undefined && timeframe && (
          <div className="text-gray-400 text-xs">
            {blocks} blocks {timeframe}
          </div>
        )}
      </div>
    </div>
  );

  return (
    <div className="space-y-6">
      {/* Analytics Cards */}
      <div className="w-full  p-6 rounded-xl border border-gray-700">
        <h2 className="text-white text-lg font-semibold mb-4">Reward Analytics</h2>
        
        {rewardHistory.length === 0 ? (
          <div className="flex items-center justify-center h-32">
            <div className="text-gray-400">Waiting for reward data...</div>
          </div>
        ) : (
          <div className="grid sm:grid-cols-1 max-md:grid-cols-2 lg:grid-cols-4 gap-4">
            <StatCard
              title="Average Per Block"
              btcValue={analytics.avgBTC}
              usdValue={analytics.avgUSD}
            />
            
            <StatCard
              title="Last Hour"
              btcValue={analytics.rewardsPerHour.BTC}
              usdValue={analytics.rewardsPerHour.USD}
              blocks={analytics.rewardsPerHour.blocks}
              timeframe="in last hour"
            />
            
            <StatCard
              title="Last Week"
              btcValue={analytics.rewardsPerWeek.BTC}
              usdValue={analytics.rewardsPerWeek.USD}
              blocks={analytics.rewardsPerWeek.blocks}
              timeframe="in last week"
            />
            
            <StatCard
              title="Last Month"
              btcValue={analytics.rewardsPerMonth.BTC}
              usdValue={analytics.rewardsPerMonth.USD}
              blocks={analytics.rewardsPerMonth.blocks}
              timeframe="in last month"
            />
          </div>
        )}
      </div>

      {/* Chart */}
      <div className="w-full h-[400px]  p-6 rounded-xl border border-gray-700">
        <div className="flex justify-between items-center mb-4">
          <h2 className="text-white text-lg font-semibold">BTC vs USD Block Rewards</h2>
          <span className="text-gray-400 text-sm">({rewardHistory.length} blocks)</span>
        </div>
        
        {rewardHistory.length === 0 ? (
          <div className="flex items-center justify-center h-full">
            <div className="text-gray-400">Waiting for block data...</div>
          </div>
        ) : (
          <ResponsiveContainer width="100%" height="90%">
            <LineChart data={rewardHistory}>
              <CartesianGrid strokeDasharray="3 3" stroke="#333" />
              <XAxis dataKey="height" stroke="#aaa" />
              <YAxis yAxisId="left" stroke="#fbbf24" domain={['auto', 'auto']} />
              <YAxis yAxisId="right" orientation="right" stroke="#60a5fa" domain={['auto', 'auto']} />
              <Tooltip />
              <Legend />
              <Line yAxisId="left" type="monotone" dataKey="rewardBTC" stroke="#fbbf24" name="BTC Reward" dot={false} />
              <Line yAxisId="right" type="monotone" dataKey="rewardUSD" stroke="#60a5fa" name="USD Reward" dot={false} />
            </LineChart>
          </ResponsiveContainer>
        )}
      </div>
    </div>
  );
}