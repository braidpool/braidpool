import { useState, useEffect } from 'react';
import { motion } from 'framer-motion';
import { Bitcoin, Clock, Calendar, Sparkles, TrendingUp, ArrowUpRight } from 'lucide-react';
import { RewardHistoryChart } from './RewardHistoryChart';
import { RewardMilestones } from './RewardMilestones';

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
}

export function RewardsDashboard() {
  const [rewardData, setRewardData] = useState<RewardData | null>(null);
  
  const [activeTab, setActiveTab] = useState('overview');
const [totalRewards, setTotalRewards] = useState(0);
  const [rewardRate, setRewardRate] = useState(0);
  const [isLoaded, setIsLoaded] = useState(false);

  useEffect(() => {
    const timer = setTimeout(() => {
      const total = (Math.random() * 10 + 10) / 1000;
      const rate = (Math.random() + 0.5) / 1000;
      setTotalRewards(total);
      setRewardRate(rate);
      setIsLoaded(true);
    }, 1000);
    return () => clearTimeout(timer);
  }, []);

  const toFixed = (val: number) => val.toFixed(2);
  useEffect(() => {
    const timer = setTimeout(() => {
      const data: RewardData = {
        totalRewards: Math.random() * 0.05 + 0.01,
        dailyAverage: Math.random() * 0.002 + 0.0005,
        weeklyProjection: Math.random() * 0.015 + 0.003,
        monthlyProjection: Math.random() * 0.06 + 0.01,
        lastReward: Math.random() * 0.003 + 0.001,
        lastRewardTime: new Date(Date.now() - Math.random() * 86400000).toISOString(),
        streak: Math.floor(Math.random() * 30) + 1,
        nextMilestone: 0.05,
        achievements: ['First Reward', 'Week Streak', '10 Beads Mined', '0.01 BTC Earned'],
      };
      setRewardData(data);
      setIsLoaded(true);
    }, 1500);
    return () => clearTimeout(timer);
  }, []);

  const formatMBTC = (btc: number) => (btc * 1000).toFixed(2);
  const timeAgo = (dateString: string) => {
    const date = new Date(dateString);
    const seconds = Math.floor((new Date().getTime() - date.getTime()) / 1000);
    let interval = seconds / 3600;
    if (interval < 1) return `${Math.floor(seconds / 60)} minutes ago`;
    if (interval < 24) return `${Math.floor(interval)} hours ago`;
    return `${Math.floor(seconds / 86400)} days ago`;
  };

  return (
    
    <div className="space-y-6">
       <motion.div
      className="border border-gray-800/50 rounded-xl bg-black/30 backdrop-blur-md p-5"
      initial={{ opacity: 0, y: 30 }}
      animate={{ opacity: isLoaded ? 1 : 0, y: isLoaded ? 0 : 30 }}
      transition={{ duration: 0.7, type: 'spring', stiffness: 100 }}
    >
      <div className="flex justify-between items-start mb-4">
        <div>
          <h3 className="text-lg font-bold text-white flex items-center">
            <Bitcoin className="h-5 w-5 text-amber-400 mr-2" />
            Reward Summary
          </h3>
          <p className="text-gray-400 text-sm mt-1">Last 30 days</p>
        </div>

        <motion.div
          className="bg-amber-500/20 p-2 rounded-lg"
          whileHover={{ scale: 1.1 }}
          transition={{ duration: 0.3 }}
        >
          <TrendingUp className="h-5 w-5 text-amber-400" />
        </motion.div>
      </div>

      {!isLoaded ? (
        <div className="space-y-3">
          <div className="h-6 bg-gray-800/50 rounded-md animate-pulse" />
          <div className="h-4 bg-gray-800/50 rounded-md animate-pulse w-3/4" />
          <div className="h-4 bg-gray-800/50 rounded-md animate-pulse w-1/2 mt-4" />
        </div>
      ) : (
        <>
          <div className="mb-4">
            <div className="text-2xl font-bold text-amber-300">
              {(totalRewards * 1000).toFixed(2)} mBTC
            </div>
            <div className="text-gray-400 text-sm">
              ${(totalRewards * 60000).toFixed(2)} USD
            </div>
          </div>

          <div className="border-t border-gray-800/50 pt-3 space-y-2">
            <div className="flex justify-between items-center">
              <div className="flex items-center text-sm text-gray-300">
                <Clock className="h-4 w-4 mr-2 text-gray-400" />
                Hourly Rate:
              </div>
              <div className="text-amber-300 font-medium text-sm flex items-center">
                {(rewardRate * 1000).toFixed(2)} mBTC
                <ArrowUpRight className="h-3 w-3 text-blue-400 ml-1" />
              </div>
            </div>

            <div className="flex justify-between items-center">
              <div className="flex items-center text-sm text-gray-300">
                <Bitcoin className="h-4 w-4 mr-2 text-gray-400" />
                USD Rate:
              </div>
              <div className="text-blue-300 font-medium text-sm flex items-center">
                ${(rewardRate * 60000).toFixed(2)}/hr
                <ArrowUpRight className="h-3 w-3 text-blue-400 ml-1" />
              </div>
            </div>
          </div>
        </>
      )}
    </motion.div>
      <div className="flex justify-between items-center">
        <div className="flex items-center gap-2">
          <Bitcoin className="h-6 w-6 text-amber-400" />
          <h2 className="text-2xl font-bold text-white">Rewards Dashboard</h2>
        </div>
        <div className="flex items-center gap-2 bg-gray-900/50 rounded-lg p-1">
          {['overview', 'history', 'achievements'].map((tab) => (
            <button
              key={tab}
              className={`px-3 py-1.5 rounded-md text-sm font-medium transition-colors ${
                activeTab === tab ? 'bg-blue-600/30 text-blue-200' : 'text-gray-400 hover:text-white'
              }`}
              onClick={() => setActiveTab(tab)}
            >
              {tab.charAt(0).toUpperCase() + tab.slice(1)}
            </button>
          ))}
        </div>
      </div>

      {!isLoaded ? (
        <div className="h-80 flex items-center justify-center">
          <div className="flex flex-col items-center">
            <div className="w-12 h-12 border-4 border-blue-500 border-t-transparent rounded-full animate-spin mb-4"></div>
            <p className="text-blue-300">Loading your rewards data...</p>
          </div>
        </div>
      ) : (
        <>
          {activeTab === 'overview' && rewardData && (
            <RewardsOverviewCards
              data={rewardData}
              formatMBTC={formatMBTC}
              timeAgo={timeAgo}
            />
          )}
          {activeTab === 'history' && <RewardHistoryChart />}
          {activeTab === 'achievements' && (
            <RewardMilestones achievements={rewardData?.achievements || []} />
          )}
        </>
      )}
    </div>
  );
}

function RewardsOverviewCards({ data, formatMBTC, timeAgo }: any) {
  const progress = (data.totalRewards / data.nextMilestone) * 100;
  return (
    <div className="grid grid-cols-2 md:grid-cols-2 xl:grid-cols-4 gap-6">
     
    
    
      <motion.div
        className="border border-gray-800/50 rounded-xl bg-black/30 backdrop-blur-md p-5"
        initial={{ opacity: 0, y: 20 }}
        animate={{ opacity: 1, y: 0 }}
        transition={{ duration: 0.5, delay: 0.2 }}
      >
        <div className="flex justify-between mb-4">
          <h3 className="text-lg font-bold text-white flex items-center">
            <Clock className="h-5 w-5 text-blue-400 mr-2" /> Live Reward Counter
          </h3>
          <div className="bg-blue-500/20 px-2 py-1 rounded text-xs font-medium text-blue-300">LIVE</div>
        </div>
        <div className="grid grid-cols-3 gap-4">
          {[{ label: 'day', value: data.dailyAverage }, { label: 'week', value: data.weeklyProjection }, { label: 'month', value: data.monthlyProjection }].map((item, i) => (
            <div key={i} className="bg-gray-900/50 rounded-lg p-3 text-center">
              <div className="text-blue-300 text-xl font-bold font-mono">{formatMBTC(item.value)}</div>
              <div className="text-gray-500 text-xs mt-1">mBTC / {item.label}</div>
            </div>
          ))}
        </div>
        <div className="mt-4 pt-4 border-t border-gray-800/50 flex justify-between">
          <div className="text-gray-400 text-sm">Last reward:</div>
          <div className="text-blue-300 font-medium">
            {formatMBTC(data.lastReward)} mBTC <span className="text-gray-500 text-xs ml-2">({timeAgo(data.lastRewardTime)})</span>
          </div>
        </div>
      </motion.div>
      {/* Mining Streak */}
      <motion.div
        className="border border-gray-800/50 rounded-xl bg-black/30 backdrop-blur-md p-5"
        initial={{ opacity: 0, y: 20 }}
        animate={{ opacity: 1, y: 0 }}
        transition={{ duration: 0.5, delay: 0.3 }}
      >
        <div className="flex justify-between mb-4">
          <h3 className="text-lg font-bold text-white flex items-center">
            <Calendar className="h-5 w-5 text-pink-400 mr-2" /> Mining Streak
          </h3>
          <div className="bg-pink-500/20 px-2 py-1 rounded text-xs font-medium text-pink-300">{data.streak} DAYS</div>
        </div>
        <div className="mb-2 text-gray-400 text-sm">Current streak</div>
        <div className="h-3 bg-gray-800 rounded-full overflow-hidden">
          <motion.div
            className="h-full bg-gradient-to-r from-pink-600 to-purple-600"
            style={{ width: `${Math.min((data.streak / 30) * 100, 100)}%` }}
            initial={{ width: 0 }}
            animate={{ width: `${Math.min((data.streak / 30) * 100, 100)}%` }}
            transition={{ duration: 1, delay: 0.5 }}
          />
        </div>
        <div className="mt-4 pt-4 border-t border-gray-800/50 text-center">
          <div className="text-gray-400 text-sm mb-2">Next streak reward in</div>
          <div className="flex justify-center gap-3">
            {[{ value: 7 - (data.streak % 7), label: 'Days' }, { value: 23, label: 'Hours' }, { value: 59, label: 'Minutes' }].map((item, i) => (
              <div key={i} className="bg-gray-900/70 rounded-lg px-3 py-2 text-center min-w-[60px]">
                <div className="text-white text-xl font-bold font-mono">{item.value}</div>
                <div className="text-gray-500 text-xs">{item.label}</div>
              </div>
            ))}
          </div>
        </div>
      </motion.div>
      {/* Next Milestone */}
      <motion.div
        className="border border-gray-800/50 rounded-xl bg-black/30 backdrop-blur-md p-5"
        initial={{ opacity: 0, y: 20 }}
        animate={{ opacity: 1, y: 0 }}
        transition={{ duration: 0.5, delay: 0.4 }}
      >
        <div className="flex justify-between mb-4">
          <h3 className="text-lg font-bold text-white flex items-center">
            <Sparkles className="h-5 w-5 text-cyan-400 mr-2" /> Next Milestone
          </h3>
        </div>
        <div className="mb-2 text-gray-400 text-sm">
          Progress to {formatMBTC(data.nextMilestone)} mBTC
        </div>
        <div className="h-3 bg-gray-800 rounded-full overflow-hidden">
          <motion.div
            className="h-full bg-gradient-to-r from-cyan-600 to-blue-600"
            style={{ width: `${Math.min(progress, 100)}%` }}
            initial={{ width: 0 }}
            animate={{ width: `${Math.min(progress, 100)}%` }}
            transition={{ duration: 1, delay: 0.5 }}
          />
        </div>
        <div className="mt-4 pt-4 border-t border-gray-800/50">
          <div className="flex justify-between">
            <div className="text-gray-400 text-sm">Remaining:</div>
            <div className="text-cyan-300 font-medium">{formatMBTC(data.nextMilestone - data.totalRewards)} mBTC</div>
          </div>
          <div className="flex justify-between mt-2">
            <div className="text-gray-400 text-sm">Estimated time:</div>
            <div className="text-cyan-300 font-medium">
              {Math.ceil((data.nextMilestone - data.totalRewards) / data.dailyAverage)} days
            </div>
          </div>
        </div>
      </motion.div>
    </div>
  );
}
