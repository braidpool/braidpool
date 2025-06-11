import { useState, useEffect } from 'react';
import {Bitcoin,Clock,Sparkles,TrendingUp,ArrowUpRight} from 'lucide-react';
import RewardHistoryChart from './RewardHistoryChart';

import { getBlockReward } from '../api/nodeApi';

interface RewardData {
  totalRewards: number;
  dailyAverage: number;
  weeklyProjection: number;
  monthlyProjection: number;
  lastReward: number;
  lastRewardTime: string;
  streak: number;
  nextMilestone: number;
  achievements: string[];
  rewardHistory: { height: number; reward: number; label: string }[]; 
}

export function RewardsDashboard() {
  const [rewardData, setRewardData] = useState<RewardData | null>(null);
  const [activeTab, setActiveTab] = useState('overview');
  const [isLoading, setIsLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);

  useEffect(() => {
    let firstLoad = true;
    let interval: NodeJS.Timeout;

    const fetchData = async () => {
      try {
        if (firstLoad) setIsLoading(true);
        const data = await getBlockReward();
        setRewardData({
          totalRewards: data.totalRewards ?? 0,
          dailyAverage: data.rewardRate ?? 0,
          weeklyProjection: data.rewardRate ? data.rewardRate * 7 : 0,
          monthlyProjection: data.rewardRate,
          lastReward: data.blockReward ?? 0,
          lastRewardTime: data.lastRewardTime ?? '',
          streak: data.streak ?? 0,
          nextMilestone: data.nextMilestone ?? 0.05,
          achievements: data.achievements ?? [],
          rewardHistory: data.rewardHistory ?? [], 
        });
        setError(null);
      } catch (err) {
        setError('Failed to load rewards data');
      } finally {
        if (firstLoad) {
          setIsLoading(false);
          firstLoad = false;
        }
      }
    };

    fetchData();
    interval = setInterval(fetchData, 1000);

    return () => clearInterval(interval);
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

  const progress = Math.min(
    (rewardData.totalRewards / rewardData.nextMilestone) * 100,
    100
  );

  return (
    <div className="space-y-6">
      <div className="flex space-x-4 mb-4">
        {['overview', 'history', 'achievements'].map((tab) => (
          <button
            key={tab}
            className={`px-4 py-2 rounded ${
              activeTab === tab
                ? 'bg-blue-600 text-white'
                : 'bg-gray-800 text-gray-300'
            }`}
            onClick={() => setActiveTab(tab)}
          >
            {tab.charAt(0).toUpperCase() + tab.slice(1)}
          </button>
        ))}
      </div>

      {activeTab === 'history' && rewardData && (
        <RewardHistoryChart rewardHistory={rewardData.rewardHistory} />
      )}

      <div className="grid grid-cols-3 md:grid-cols-2 xl:grid-cols-4 gap-6">
        {/* Reward Summary */}
        <div className="border border-gray-800/50 rounded-xl bg-black/30 p-5">
          <div className="flex justify-between items-start mb-4">
            <div>
              <h3 className="text-lg font-bold text-white flex items-center">
                <Bitcoin className="h-5 w-5 text-amber-400 mr-2" />
                Reward Summary
              </h3>
              <p className="text-gray-400 text-sm mt-1">Last 30 days</p>
            </div>
            <div className="bg-amber-500/20 p-2 rounded-lg">
              <TrendingUp className="h-5 w-5 text-amber-400" />
            </div>
          </div>
          <div className="mb-4">
            <div className="text-2xl font-bold text-amber-300">
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
              <div className="text-amber-300 font-medium text-sm flex items-center">
                {formatMBTC(rewardData.dailyAverage / 24)} mBTC
                <ArrowUpRight className="h-3 w-3 text-blue-400 ml-1" />
              </div>
            </div>
            <div className="flex justify-between items-center">
              <div className="flex items-center text-sm text-gray-300">
                <Bitcoin className="h-4 w-4 mr-2 text-gray-400" />
                USD Rate:
              </div>
              <div className="text-blue-300 font-medium text-sm flex items-center">
                ${((rewardData.dailyAverage / 24) * 60000).toFixed(2)}/hr
                <ArrowUpRight className="h-3 w-3 text-blue-400 ml-1" />
              </div>
            </div>
          </div>
        </div>
        {/* Live Reward Counter */}
        <div className="border border-gray-800/50 rounded-xl bg-black/30 p-5">
          <div className="flex justify-between mb-4">
            <h3 className="text-lg font-bold text-white flex items-center">
              <Clock className="h-5 w-5 text-blue-400 mr-2" /> Live Reward
              Counter
            </h3>
            <div className="bg-blue-500/20 px-2 py-1 rounded text-xs font-medium text-blue-300">
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
                <div className="text-blue-300 text-xl font-bold font-mono">
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
            <div className="text-blue-300 font-medium">
              {formatMBTC(rewardData.lastReward)} mBTC
              <span className="text-gray-500 text-xs ml-2">
                ({timeAgo(rewardData.lastRewardTime)})
              </span>
            </div>
          </div>
        </div>

        
      </div>
    </div>
  );
}
