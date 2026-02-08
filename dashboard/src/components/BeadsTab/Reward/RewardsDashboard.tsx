import React, { useEffect, useRef, useState } from 'react';
import {
  LineChart,
  Line,
  XAxis,
  YAxis,
  Tooltip,
  Legend,
  ResponsiveContainer,
  CartesianGrid,
} from 'recharts';
import { calculateRewardAnalytics } from '../lib/Utils';
import { RewardPoint } from '../lib/Types';
import { StatCard } from './RewardStats';
import { WEBSOCKET_URLS } from '@/URLs';

export function RewardsDashboard() {
  const [rewardHistory, setRewardHistory] = useState<RewardPoint[]>([]);
  const wsRef = useRef<WebSocket | null>(null);

  useEffect(() => {
    const ws = new WebSocket(WEBSOCKET_URLS.MAIN_WEBSOCKET);
    wsRef.current = ws;
    let isMounted = true;

    ws.onopen = () => {
      if (!isMounted) return;
      console.log('WebSocket connected');
    };

    ws.onmessage = (event) => {
      if (!isMounted) return;
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

            setRewardHistory(parsedData);
          } else {
            console.error('Expected array but got:', typeof rawData, rawData);
          }
        }
      } catch (err) {
        console.error('WebSocket JSON error:', err);
      }
    };

    ws.onerror = (error) => {
      console.error('WebSocket error:', error);
    };

    ws.onclose = () => {
      if (!isMounted) return;
      console.log('WebSocket disconnected');
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
  }, []);

  const analytics = calculateRewardAnalytics(rewardHistory);

  return (
    <div className="space-y-6">
      {/* Analytics Cards */}
      <div className="w-full bg-paper p-6 rounded-xl border border-border">
        <h2 className="text-textPrimary text-lg font-semibold mb-4">
          Reward Analytics
        </h2>

        {rewardHistory.length === 0 ? (
          <div className="flex items-center justify-center h-32">
            <div className="text-textSecondary">Waiting for reward data...</div>
          </div>
        ) : (
          <div className="grid sm:grid-cols-1 md:grid-cols-2 lg:grid-cols-4 gap-4">
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

      {/* Block Rewards Chart */}
      <div className="w-full bg-paper p-6 rounded-xl border border-border">
        <div className="flex justify-between items-center mb-4">
          <h2 className="text-textPrimary text-lg font-semibold">
            Block Rewards
          </h2>
          <span className="text-sm text-textSecondary">
            ({rewardHistory.length} blocks)
          </span>
        </div>
        <ResponsiveContainer width="100%" height={400}>
          <LineChart
            data={rewardHistory}
            margin={{ top: 5, right: 20, left: 30, bottom: 5 }}
          >
            <CartesianGrid strokeDasharray="3 3" stroke="var(--color-border)" />
            <XAxis
              dataKey="height"
              type="number"
              domain={['dataMin', 'dataMax']}
              tick={{ fill: 'var(--color-text-secondary)' }}
              stroke="var(--color-border)"
            />
            <YAxis
              yAxisId="left"
              orientation="left"
              tick={{ fill: 'var(--color-text-secondary)' }}
              stroke="var(--color-border)"
            />
            <YAxis
              yAxisId="right"
              orientation="right"
              tick={{ fill: 'var(--color-text-secondary)' }}
              stroke="var(--color-border)"
            />
            <Tooltip
              contentStyle={{
                backgroundColor: 'var(--color-paper)',
                border: '1px solid var(--color-border)',
                color: 'var(--color-text-primary)',
              }}
            />
            <Legend wrapperStyle={{ color: 'var(--color-text-primary)' }} />
            <Line
              yAxisId="left"
              type="monotone"
              dataKey="rewardBTC"
              stroke="#8884d8"
              name="Reward (BTC)"
            />
            <Line
              yAxisId="right"
              type="monotone"
              dataKey="rewardUSD"
              stroke="#82ca9d"
              name="Reward (USD)"
            />
          </LineChart>
        </ResponsiveContainer>
      </div>
    </div>
  );
}
