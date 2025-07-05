import { useState, useEffect, useRef } from 'react';
import { Bitcoin, Clock, TrendingUp, ArrowUpRight } from 'lucide-react';
import RewardHistoryChart from './RewardHistoryChart';
import { RewardData } from '../lib/Types';
import { generateRewardHistory } from './generateRewardHistory';
import AnimatedStatCard from '../AnimatedStatCard';
import { processRewardsData } from '../lib/Utils';

export function RewardsDashboard() {
  const [rewardData, setRewardData] = useState<RewardData | null>(null);
  const [bitcoinPrice, setBitcoinPrice] = useState<number>(0);
  const [activeTab, setActiveTab] = useState('overview');
  const [isLoading, setIsLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [isConnected, setIsConnected] = useState(false);
  const wsRef = useRef<WebSocket | null>(null);

  useEffect(() => {
    const ws = new WebSocket('ws://localhost:5000');
    let isMounted = true;
    wsRef.current = ws;
    ws.onopen = () => {
      if (!isMounted) return;
      setIsConnected(true);
      setIsLoading(false);
    };

    ws.onerror = (error) => {
      setIsConnected(false);
      setError('WebSocket connection failed');
      console.error('WebSocket error:', error);
    };
    ws.onmessage = (event) => {
      if (!isMounted) return;
      try {
        const message = JSON.parse(event.data);
        if (message.type === 'rewards_data') {
          const processed = processRewardsData(message.data);
          const rewardHistory = generateRewardHistory(
            processed.blockCount,
            processed.blockReward
          );
          setRewardData({
            totalRewards: processed.totalRewards ?? 0,
            dailyAverage: processed.rewardRate ?? 0,
            weeklyProjection: (processed.rewardRate ?? 0) * 7,
            monthlyProjection: (processed.rewardRate ?? 0) * 30,
            lastReward: processed.blockReward ?? 0,
            lastRewardTime: processed.lastRewardTime ?? '',
            rewardHistory: rewardHistory ?? [],
          });
          setIsLoading(false);
          setError(null);
        } else if (message.type === 'bitcoin_update') {
          const priceData = message.data.price;
          if (priceData && priceData.USD) {
            setBitcoinPrice(parseFloat(priceData.USD));
          }
        }
      } catch (e) {
        setError('WebSocket message parse error');
        console.error('WebSocket message parse error:', e);
      }
    };
    ws.onclose = () => {
      if (!isMounted) return;
      console.log('WebSocket disconnected');
      setIsConnected(false);
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

  if (isLoading || !isConnected) {
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

      <div className="grid grid-cols-1 md:grid-cols-2 xl:grid-cols-4 gap-6 ">
        {/* Reward Summary */}
        {activeTab === 'overview' && (
          <>
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
                  ${(rewardData.totalRewards * bitcoinPrice).toFixed(2)} USD
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
                    $
                    {((rewardData.dailyAverage / 24) * bitcoinPrice).toFixed(2)}
                    /hr
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
              <div className="grid sm:grid-cols-1 md:grid-cols-2 lg:grid-cols-3 gap-6">
                <AnimatedStatCard
                  title="mBTC / day"
                  value={formatMBTC(rewardData.dailyAverage)}
                />
                <AnimatedStatCard
                  title="mBTC / week"
                  value={formatMBTC(rewardData.weeklyProjection)}
                />
                <AnimatedStatCard
                  title="mBTC/month"
                  value={formatMBTC(rewardData.monthlyProjection)}
                />
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
          </>
        )}
      </div>
    </div>
  );
}
