'use client';

import { useState, useEffect } from 'react';
import { motion } from 'framer-motion';
import { Bitcoin, Clock, Calendar, Sparkles } from 'lucide-react';
import { RewardSummaryCard } from './RewardSummaryCard';
import { RewardHistoryChart } from './RewardHistoryChart';
import { RewardMilestones } from './RewardMilestones';

interface RewardData {
  totalRewards: number; // in BTC
  dailyAverage: number; // in BTC
  weeklyProjection: number; // in BTC
  monthlyProjection: number; // in BTC
  lastReward: number; // in BTC
  lastRewardTime: string;
  streak: number; // days
  nextMilestone: number; // in BTC
  achievements: string[];
}

export function RewardsDashboard() {
  const [rewardData, setRewardData] = useState<RewardData | null>(null);
  const [isLoaded, setIsLoaded] = useState(false);
  const [activeTab, setActiveTab] = useState('overview');

  // Simulate loading data
  useEffect(() => {
    const timer = setTimeout(() => {
      // Generate random reward data
      const data: RewardData = {
        totalRewards: Math.random() * 0.05 + 0.01, // 0.01-0.06 BTC
        dailyAverage: Math.random() * 0.002 + 0.0005, // 0.0005-0.0025 BTC
        weeklyProjection: Math.random() * 0.015 + 0.003, // 0.003-0.018 BTC
        monthlyProjection: Math.random() * 0.06 + 0.01, // 0.01-0.07 BTC
        lastReward: Math.random() * 0.003 + 0.001, // 0.001-0.004 BTC
        lastRewardTime: new Date(
          Date.now() - Math.random() * 86400000
        ).toISOString(),
        streak: Math.floor(Math.random() * 30) + 1,
        nextMilestone: 0.05,
        achievements: [
          'First Reward',
          'Week Streak',
          '10 Beads Mined',
          '0.01 BTC Earned',
        ],
      };

      setRewardData(data);
      setIsLoaded(true);
    }, 1500);

    return () => clearTimeout(timer);
  }, []);

  // Convert BTC to mBTC
  const formatMBTC = (btc: number) => (btc * 1000).toFixed(2);

  // Calculate USD value (assuming 1 BTC = $60,000)
  const formatUSD = (btc: number) => (btc * 60000).toFixed(2);

  // Format time ago
  const timeAgo = (dateString: string) => {
    const date = new Date(dateString);
    const seconds = Math.floor((new Date().getTime() - date.getTime()) / 1000);

    let interval = seconds / 3600;
    if (interval < 1) {
      interval = seconds / 60;
      return `${Math.floor(interval)} minutes ago`;
    }
    if (interval < 24) {
      return `${Math.floor(interval)} hours ago`;
    }
    interval = seconds / 86400;
    return `${Math.floor(interval)} days ago`;
  };

  return (
    <div className="space-y-6">
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
                activeTab === tab
                  ? 'bg-blue-600/30 text-blue-200'
                  : 'text-gray-400 hover:text-white'
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
            <div className="grid grid-cols-1 md:grid-cols-2 gap-6">
              <div className="space-y-6">
                <RewardSummaryCard />

                {/* Live Reward Counter */}
                <motion.div
                  className="relative border border-gray-800/50 rounded-xl bg-black/30 backdrop-blur-md overflow-hidden p-5"
                  initial={{ opacity: 0, y: 20 }}
                  animate={{ opacity: 1, y: 0 }}
                  transition={{ duration: 0.5, delay: 0.2 }}
                >
                  <div className="absolute inset-0 p-[1px] rounded-xl overflow-hidden pointer-events-none">
                    <motion.div
                      className="absolute inset-0 "
                      animate={{
                        backgroundPosition: ['0% 0%', '200% 0%'],
                      }}
                      transition={{
                        duration: 8,
                        repeat: Number.POSITIVE_INFINITY,
                        repeatType: 'loop',
                        ease: 'linear',
                      }}
                    />
                  </div>

                  <div className="relative z-10">
                    <div className="flex justify-between items-start mb-4">
                      <h3 className="text-lg font-bold text-white flex items-center">
                        <Clock className="h-5 w-5 text-blue-400 mr-2" />
                        Live Reward Counter
                      </h3>
                      <div className="bg-blue-500/20 px-2 py-1 rounded text-xs font-medium text-blue-300">
                        LIVE
                      </div>
                    </div>

                    <div className="flex items-center justify-center py-4">
                      <div className="text-center">
                        <div className="text-gray-400 text-sm mb-1">
                          Estimated earnings per
                        </div>
                        <div className="grid grid-cols-3 gap-4 mt-2">
                          <div className="bg-gray-900/50 rounded-lg p-3 text-center">
                            <div className="text-blue-300 text-xl font-bold font-mono">
                              {formatMBTC(rewardData.dailyAverage)}
                            </div>
                            <div className="text-gray-500 text-xs mt-1">
                              mBTC / day
                            </div>
                          </div>
                          <div className="bg-gray-900/50 rounded-lg p-3 text-center">
                            <div className="text-blue-300 text-xl font-bold font-mono">
                              {formatMBTC(rewardData.weeklyProjection)}
                            </div>
                            <div className="text-gray-500 text-xs mt-1">
                              mBTC / week
                            </div>
                          </div>
                          <div className="bg-gray-900/50 rounded-lg p-3 text-center">
                            <div className="text-blue-300 text-xl font-bold font-mono">
                              {formatMBTC(rewardData.monthlyProjection)}
                            </div>
                            <div className="text-gray-500 text-xs mt-1">
                              mBTC / month
                            </div>
                          </div>
                        </div>
                      </div>
                    </div>

                    <div className="mt-4 pt-4 border-t border-gray-800/50">
                      <div className="flex justify-between items-center">
                        <div className="text-gray-400 text-sm">
                          Last reward:
                        </div>
                        <div className="flex items-center">
                          <span className="text-blue-300 font-medium">
                            {formatMBTC(rewardData.lastReward)} mBTC
                          </span>
                          <span className="text-gray-500 text-xs ml-2">
                            ({timeAgo(rewardData.lastRewardTime)})
                          </span>
                        </div>
                      </div>
                    </div>
                  </div>
                </motion.div>
              </div>

              <div className="space-y-6">
                {/* Mining Streak */}
                <motion.div
                  className="relative border border-gray-800/50 rounded-xl bg-black/30 backdrop-blur-md overflow-hidden p-5"
                  initial={{ opacity: 0, y: 20 }}
                  animate={{ opacity: 1, y: 0 }}
                  transition={{ duration: 0.5, delay: 0.3 }}
                >
                  <div className="absolute inset-0 p-[1px] rounded-xl overflow-hidden pointer-events-none">
                    <motion.div
                      className="absolute inset-0 "
                      animate={{
                        backgroundPosition: ['0% 0%', '200% 0%'],
                      }}
                      transition={{
                        duration: 8,
                        repeat: Number.POSITIVE_INFINITY,
                        repeatType: 'loop',
                        ease: 'linear',
                      }}
                    />
                  </div>

                  <div className="relative z-10">
                    <div className="flex justify-between items-start mb-4">
                      <h3 className="text-lg font-bold text-white flex items-center">
                        <Calendar className="h-5 w-5 text-pink-400 mr-2" />
                        Mining Streak
                      </h3>
                      <div className="bg-pink-500/20 px-2 py-1 rounded text-xs font-medium text-pink-300">
                        {rewardData.streak} DAYS
                      </div>
                    </div>

                    <div className="flex items-center justify-center py-4">
                      <div className="w-full">
                        <div className="flex justify-between mb-2">
                          <span className="text-gray-400 text-sm">
                            Current streak
                          </span>
                          <span className="text-pink-300 font-medium">
                            {rewardData.streak} days
                          </span>
                        </div>

                        <div className="h-3 bg-gray-800 rounded-full overflow-hidden">
                          <motion.div
                            className="h-full bg-gradient-to-r from-pink-600 to-purple-600"
                            style={{
                              width: `${Math.min((rewardData.streak / 30) * 100, 100)}%`,
                            }}
                            initial={{ width: 0 }}
                            animate={{
                              width: `${Math.min((rewardData.streak / 30) * 100, 100)}%`,
                            }}
                            transition={{ duration: 1, delay: 0.5 }}
                          />
                        </div>

                        <div className="flex justify-between mt-1">
                          <span className="text-gray-500 text-xs">0</span>
                          <span className="text-gray-500 text-xs">30 days</span>
                        </div>

                        <div className="mt-4 pt-4 border-t border-gray-800/50">
                          <div className="text-center">
                            <div className="text-gray-400 text-sm mb-2">
                              Next streak reward in
                            </div>
                            <div className="flex justify-center gap-3">
                              {[
                                {
                                  value: 7 - (rewardData.streak % 7),
                                  label: 'Days',
                                },
                                { value: 23, label: 'Hours' },
                                { value: 59, label: 'Minutes' },
                              ].map((item, i) => (
                                <div
                                  key={i}
                                  className="bg-gray-900/70 rounded-lg px-3 py-2 text-center min-w-[60px]"
                                >
                                  <div className="text-white text-xl font-bold font-mono">
                                    {item.value}
                                  </div>
                                  <div className="text-gray-500 text-xs">
                                    {item.label}
                                  </div>
                                </div>
                              ))}
                            </div>
                          </div>
                        </div>
                      </div>
                    </div>
                  </div>
                </motion.div>

                {/* Next Milestone */}
                <motion.div
                  className="relative border border-gray-800/50 rounded-xl bg-black/30 backdrop-blur-md overflow-hidden p-5"
                  initial={{ opacity: 0, y: 20 }}
                  animate={{ opacity: 1, y: 0 }}
                  transition={{ duration: 0.5, delay: 0.4 }}
                >
                  <div className="absolute inset-0 p-[1px] rounded-xl overflow-hidden pointer-events-none">
                    <motion.div
                      className="absolute inset-0 "
                      animate={{
                        backgroundPosition: ['0% 0%', '200% 0%'],
                      }}
                      transition={{
                        duration: 8,
                        repeat: Number.POSITIVE_INFINITY,
                        repeatType: 'loop',
                        ease: 'linear',
                      }}
                    />
                  </div>

                  <div className="relative z-10">
                    <div className="flex justify-between items-start mb-4">
                      <h3 className="text-lg font-bold text-white flex items-center">
                        <Sparkles className="h-5 w-5 text-cyan-400 mr-2" />
                        Next Milestone
                      </h3>
                    </div>

                    <div className="flex items-center justify-center py-4">
                      <div className="w-full">
                        <div className="flex justify-between mb-2">
                          <span className="text-gray-400 text-sm">
                            Progress to {formatMBTC(rewardData.nextMilestone)}{' '}
                            mBTC
                          </span>
                          <span className="text-cyan-300 font-medium">
                            {Math.round(
                              (rewardData.totalRewards /
                                rewardData.nextMilestone) *
                                100
                            )}
                            %
                          </span>
                        </div>

                        <div className="h-3 bg-gray-800 rounded-full overflow-hidden">
                          <motion.div
                            className="h-full bg-gradient-to-r from-cyan-600 to-blue-600"
                            initial={{ width: 0 }}
                            animate={{
                              width: `${Math.min((rewardData.totalRewards / rewardData.nextMilestone) * 100, 100)}%`,
                            }}
                            transition={{ duration: 1, delay: 0.5 }}
                          />
                        </div>

                        <div className="flex justify-between mt-1">
                          <span className="text-gray-500 text-xs">0</span>
                          <span className="text-gray-500 text-xs">
                            {formatMBTC(rewardData.nextMilestone)} mBTC
                          </span>
                        </div>

                        <div className="mt-4 pt-4 border-t border-gray-800/50">
                          <div className="flex justify-between items-center">
                            <div className="text-gray-400 text-sm">
                              Remaining:
                            </div>
                            <div className="text-cyan-300 font-medium">
                              {formatMBTC(
                                rewardData.nextMilestone -
                                  rewardData.totalRewards
                              )}{' '}
                              mBTC
                            </div>
                          </div>
                          <div className="flex justify-between items-center mt-2">
                            <div className="text-gray-400 text-sm">
                              Estimated time:
                            </div>
                            <div className="text-cyan-300 font-medium">
                              {Math.ceil(
                                (rewardData.nextMilestone -
                                  rewardData.totalRewards) /
                                  rewardData.dailyAverage
                              )}{' '}
                              days
                            </div>
                          </div>
                        </div>
                      </div>
                    </div>
                  </div>
                </motion.div>
              </div>
            </div>
          )}

          {activeTab === 'history' && (
            <div className="space-y-6">
              <RewardHistoryChart />
            </div>
          )}

          {activeTab === 'achievements' && (
            <div className="space-y-6">
              <RewardMilestones achievements={rewardData?.achievements || []} />
            </div>
          )}
        </>
      )}
    </div>
  );
}
