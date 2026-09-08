import React, { useEffect, useState } from 'react';
import { calculateRewardAnalytics } from '../lib/Utils';
import { RewardPoint } from '../lib/Types';
import { StatCard } from './RewardStats';
import { WEBSOCKET_URLS } from '@/URLs';
import TwoLineChart from '../../common/charts/TwoLineChart';

export function RewardsDashboard() {
  const [rewardHistory, setRewardHistory] = useState<RewardPoint[]>([]);

  useEffect(() => {
    const ws = new WebSocket(WEBSOCKET_URLS.MAIN_WEBSOCKET);
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

      {rewardHistory.length === 0 ? (
        <div className="w-full h-[400px] p-6 rounded-xl border border-gray-700">
          <div className="flex justify-between items-center mb-4">
            <h2 className="text-white text-lg font-semibold">Block Rewards</h2>
            <span className="text-gray-400 text-sm">(0 blocks)</span>
          </div>
          <div className="flex items-center justify-center h-[90%]">
            <div className="text-gray-400">Waiting for block data...</div>
          </div>
        </div>
      ) : (
        <TwoLineChart
          data={rewardHistory}
          xAxisKey="height"
          series={[
            { dataKey: 'rewardBTC', label: 'BTC Reward', color: '#fbbf24' },
            {
              dataKey: 'rewardUSD',
              label: 'USD Reward',
              color: '#60a5fa',
              yAxisId: 'right',
            },
          ]}
          title="Block Rewards"
          description={`(${rewardHistory.length} blocks)`}
          downloadFileName="block-rewards-chart"
          showLegend
          dualAxis
        />
      )}
    </div>
  );
}
