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
      <div className="w-full  p-6 rounded-xl border border-gray-700">
        <h2 className="text-white text-lg font-semibold mb-4">
          Reward Analytics
        </h2>

        {rewardHistory.length === 0 ? (
          <div className="flex items-center justify-center h-32">
            <div className="text-gray-400">Waiting for reward data...</div>
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

      {/* Chart */}
      <div className="w-full h-[400px]  p-6 rounded-xl border border-gray-700">
        <div className="flex justify-between items-center mb-4">
          <h2 className="text-white text-lg font-semibold">Block Rewards</h2>
          <span className="text-gray-400 text-sm">
            ({rewardHistory.length} blocks)
          </span>
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
              <YAxis
                yAxisId="left"
                stroke="#fbbf24"
                domain={['auto', 'auto']}
              />
              <YAxis
                yAxisId="right"
                orientation="right"
                stroke="#60a5fa"
                domain={['auto', 'auto']}
              />
              <Tooltip
                content={({ active, payload, label }) => {
                  if (active && payload && payload.length) {
                    const timestamp = payload[0]?.payload?.timestamp;
                    const formattedTime = timestamp
                      ? new Date(timestamp).toLocaleTimeString()
                      : 'N/A';

                    return (
                      <div className=" bg-[#1a1a1a] text-gray-400 sm:text-xs md:text-base border border-xl border-gray-500 p-2 rounded-sm">
                        <p>Height: {label}</p>
                        <p>Time: {formattedTime}</p>
                        {payload.map((item, index) => {
                          const value =
                            typeof item.value === 'number'
                              ? item.value.toFixed(2)
                              : item.value;
                          return (
                            <p key={index}>
                              {item.name}: {value}
                            </p>
                          );
                        })}
                      </div>
                    );
                  }
                  return null;
                }}
              />

              <Legend />
              <Line
                yAxisId="left"
                type="monotone"
                dataKey="rewardBTC"
                stroke="#fbbf24"
                name="BTC Reward"
                dot={false}
              />
              <Line
                yAxisId="right"
                type="monotone"
                dataKey="rewardUSD"
                stroke="#60a5fa"
                name="USD Reward"
                dot={false}
              />
            </LineChart>
          </ResponsiveContainer>
        )}
      </div>
    </div>
  );
}
