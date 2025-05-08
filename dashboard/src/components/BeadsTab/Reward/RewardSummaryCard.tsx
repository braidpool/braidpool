'use client';

import { motion } from 'framer-motion';
import { Bitcoin, TrendingUp, ArrowUpRight, Clock } from 'lucide-react';
import { useState, useEffect } from 'react';

export function RewardSummaryCard() {
  const [totalRewards, setTotalRewards] = useState(0);
  const [rewardRate, setRewardRate] = useState(0);
  const [isLoaded, setIsLoaded] = useState(false);

  // Simulate loading data
  useEffect(() => {
    // Generate random total rewards between 10-20 mBTC
    const randomTotal = (Math.random() * 10 + 10) / 1000; // Convert to BTC

    // Generate random reward rate between 0.5-1.5 mBTC per hour
    const randomRate = (Math.random() + 0.5) / 1000; // Convert to BTC

    const timer = setTimeout(() => {
      setTotalRewards(randomTotal);
      setRewardRate(randomRate);
      setIsLoaded(true);
    }, 1000);

    return () => clearTimeout(timer);
  }, []);

  // Convert BTC to mBTC
  const mBTCTotal = totalRewards * 1000;
  const mBTCRate = rewardRate * 1000;

  // Calculate USD values (assuming 1 BTC = $60,000)
  const usdTotal = totalRewards * 60000;
  const usdRate = rewardRate * 60000;

  return (
    <motion.div
      className="relative border border-gray-800/50 rounded-xl bg-black/30 backdrop-blur-md overflow-hidden p-5"
      initial={{ opacity: 0, y: 30 }}
      animate={{ opacity: isLoaded ? 1 : 0, y: isLoaded ? 0 : 30 }}
      transition={{ duration: 0.7, type: 'spring', stiffness: 100 }}
    >
      {/* Animated border gradient */}
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
          <div>
            <h3 className="text-lg font-bold text-white flex items-center">
              <Bitcoin className="h-5 w-5 text-amber-400 mr-2" />
              Reward Summary
            </h3>
            <p className="text-gray-400 text-sm mt-1">Last 30 days</p>
          </div>

          <motion.div
            className="bg-amber-500/20 p-2 rounded-lg"
            whileHover={{ scale: 1.1, rotate: 5 }}
            animate={{ scale: [1, 1.05, 1] }}
            transition={{
              duration: 2,
              repeat: Number.POSITIVE_INFINITY,
              repeatType: 'reverse',
            }}
          >
            <TrendingUp className="h-5 w-5 text-amber-400" />
          </motion.div>
        </div>

        {!isLoaded ? (
          <div className="space-y-3">
            <div className="h-6 bg-gray-800/50 rounded-md animate-pulse"></div>
            <div className="h-4 bg-gray-800/50 rounded-md animate-pulse w-3/4"></div>
            <div className="h-4 bg-gray-800/50 rounded-md animate-pulse w-1/2 mt-4"></div>
          </div>
        ) : (
          <>
            <div className="mb-4">
              <div className="text-2xl font-bold text-amber-300">
                {mBTCTotal.toFixed(2)} mBTC
              </div>
              <div className="text-gray-400 text-sm">
                ${usdTotal.toFixed(2)} USD
              </div>
            </div>

            <div className="flex items-center justify-between pt-3 border-t border-gray-800/50">
              <div className="flex items-center">
                <Clock className="h-4 w-4 text-gray-400 mr-2" />
                <span className="text-gray-300 text-sm">Hourly Rate:</span>
              </div>

              <div className="flex items-center">
                <span className="text-amber-300 font-medium text-sm mr-1">
                  {mBTCRate.toFixed(2)} mBTC
                </span>
                <ArrowUpRight className="h-3 w-3 text-blue-400" />
              </div>
            </div>

            <div className="flex items-center justify-between pt-2">
              <div className="flex items-center">
                <Bitcoin className="h-4 w-4 text-gray-400 mr-2" />
                <span className="text-gray-300 text-sm">USD Rate:</span>
              </div>

              <div className="flex items-center">
                <span className="text-blue-300 font-medium text-sm mr-1">
                  ${usdRate.toFixed(2)}/hr
                </span>
                <ArrowUpRight className="h-3 w-3 text-blue-400" />
              </div>
            </div>
          </>
        )}
      </div>
    </motion.div>
  );
}
