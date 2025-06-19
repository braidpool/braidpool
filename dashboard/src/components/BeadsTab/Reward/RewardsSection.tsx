import { useState, useEffect } from 'react';
import { Bitcoin, Clock, TrendingUp, ArrowUpRight } from 'lucide-react';
import RewardHistoryChart from './RewardHistoryChart';
import { RewardData } from '../lib/types';

export function RewardsDashboard() {
  const [rewardData, setRewardData] = useState<RewardData | null>(null);
  const [activeTab, setActiveTab] = useState('overview');
  const [isLoading, setIsLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  useEffect(() => {
    const ws = new WebSocket('ws://localhost:5000');

    ws.onopen = () => {
      console.log('[✓] Rewards WebSocket connected');
    };

    ws.onmessage = (event) => {
      try {
        const message = JSON.parse(event.data);
        if (message.type === 'Rewards_update') {
          const data = message.data;
          setRewardData({
            totalRewards: data.totalRewards ?? 0,
            dailyAverage: data.rewardRate ?? 0,
            weeklyProjection: (data.rewardRate ?? 0) * 7,
            monthlyProjection: (data.rewardRate ?? 0) * 30,
            lastReward: data.blockReward ?? 0,
            lastRewardTime: data.lastRewardTime ?? '',
            streak: data.streak ?? 0,
            nextMilestone: data.nextMilestone ?? 0.05,
            achievements: data.achievements ?? [],
            rewardHistory: data.rewardHistory ?? [],
          });
          setIsLoading(false);
          setError(null);
        }
      } catch (err) {
        console.error('Failed to parse reward WebSocket message:', err);
      }
    };

    ws.onerror = (err) => {
      console.error('WebSocket error:', err);
      setError('WebSocket connection failed');
    };

    ws.onclose = () => {
      console.warn('Rewards WebSocket disconnected');
    };

    return () => ws.close();
  }, []);

  const formatMBTC = (btc: number) => (btc * 1000).toFixed(2);

  const timeAgo = (dateString: string) => {
    if (!dateString) return '';
    const seconds = Math.floor(
      (Date.now() - new Date(dateString).getTime()) / 1000
    );
    const interval = seconds / 3600;
    if (interval < 1) return `${Math.floor(seconds / 60)} minutes ago`;
    if (interval < 24) return `${Math.floor(interval)} hours ago`;
    return `${Math.floor(seconds / 86400)} days ago`;
  };

  if (isLoading) {
    return (
      <div className="h-80 flex items-center justify-center">
        <p className="text-blue-300">Loading your rewards data...</p>
      </div>
    );
  }

  if (error) {
    return (
      <div className="h-80 flex items-center justify-center text-red-400">
        {error}
      </div>
    );
  }

  if (!rewardData) return null;

  return (
    <div className="space-y-6 bg-[#1c1c1c]">
      <div className="flex justify-between items-center">
        <div className="flex items-center gap-2">
          <h2 className="text-xl font-bold text-white tracking-tighter">
            Rewards Dashboard
          </h2>
        </div>
        <div className="flex space-x-4 mb-4">
          {['overview', 'history'].map((tab) => (
            <button
              key={tab}
              className={`px-4 py-2 rounded-lg ${
                activeTab === tab
                  ? 'bg-gray-700 text-white'
                  : 'bg-black text-gray-300'
              }`}
              onClick={() => setActiveTab(tab)}
            >
              {tab.charAt(0).toUpperCase() + tab.slice(1)}
            </button>
          ))}
        </div>
      </div>
      {activeTab === 'history' && rewardData && (
        <RewardHistoryChart rewardHistory={rewardData.rewardHistory} />
      )}

      <div className="grid grid-cols-2 md:grid-cols-2 xl:grid-cols-4 gap-6 ">
        {/* Reward Summary */}
        <div className="bg-[#1c1c1c] border border-gray-700 rounded-xl backdrop-blur-sm p-5">
          <div className="flex justify-between items-start mb-4">
            <div>
              <h3 className="text-md font-bold text-white flex items-center">
                <Bitcoin className="h-4 w-4 text-amber-400 mr-2" />
                Reward Summary
              </h3>
              <p className="text-gray-400 text-sm mt-1">Last 30 days</p>
            </div>
            <div className=" p-2 rounded-lg">
              <TrendingUp className="h-5 w-5 text-white" />
            </div>
          </div>
          <div className="mb-4">
            <div className="text-xl font-bold text-white">
              {formatMBTC(rewardData.totalRewards)} mBTC
            </div>
            <div className="text-gray-400 text-sm">
              ${(rewardData.totalRewards * 60000).toFixed(2)} USD
            </div>
          </div>
          <div className="border-t border-gray-800/50 pt-3 space-y-2">
            <div className="flex justify-between items-center">
              <div className="flex items-center text-sm text-gray-300">
                <Clock className="h-4 w-4 mr-2 text-gray-400" />
                Hourly Rate:
              </div>
              <div className="text-white font-small text-sm flex items-center">
                {formatMBTC(rewardData.dailyAverage / 24)} mBTC
                <ArrowUpRight className="h-3 w-3 text-blue-400 ml-1" />
              </div>
            </div>
            <div className="flex justify-between items-center">
              <div className="flex items-center text-sm text-gray-300">
                <Bitcoin className="h-4 w-4 mr-2 text-gray-400" />
                USD Rate:
              </div>
              <div className="text-white font-small text-sm flex items-center">
                ${((rewardData.dailyAverage / 24) * 60000).toFixed(2)}/hr
                <ArrowUpRight className="h-3 w-3 text-blue-400 ml-1" />
              </div>
            </div>
          </div>
        </div>
        {/* Live Reward Counter */}
        <div className=" bg-[#1c1c1c] border border-gray-700 rounded-xl backdrop-blur-sm p-5">
          <div className="flex justify-between mb-4">
            <h3 className="text-md font-bold text-white flex items-center">
              <Clock className="h-5 w-5 text-blue-400 mr-2" /> Live Reward
              Counter
            </h3>
            <div className="px-2 py-1 rounded text-xs font-medium text-white">
              LIVE
            </div>
          </div>
          <div className="grid grid-cols-3 gap-4">
            {[
              { label: 'day', value: rewardData.dailyAverage },
              { label: 'week', value: rewardData.weeklyProjection },
              { label: 'month', value: rewardData.monthlyProjection },
            ].map((item) => (
              <div
                key={item.label}
                className="bg-gray-900/50 rounded-lg p-3 text-center"
              >
                <div className="text-white text-xl font-bold font-mono">
                  {formatMBTC(item.value)}
                </div>
                <div className="text-gray-500 text-xs mt-1">
                  mBTC / {item.label}
                </div>
              </div>
            ))}
          </div>
          <div className="mt-4 pt-4 border-t border-gray-800/50 flex justify-between">
            <div className="text-gray-400 text-sm">Last reward:</div>
            <div className="text-white font-medium">
              {formatMBTC(rewardData.lastReward)} mBTC
              <span className="text-gray-500 text-xs ml-2">
                {timeAgo(rewardData.lastRewardTime)}
              </span>
            </div>
          </div>
        </div>
      </div>
    </div>
  );
}
