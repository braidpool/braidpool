'use client';

import type React from 'react';

import { useState, useEffect, useRef } from 'react';
import { motion } from 'framer-motion';
import {
  Calendar,
  Download,
  Filter,
  ArrowUpRight,
  ArrowDownRight,
} from 'lucide-react';

interface RewardDataPoint {
  date: string;
  amount: number; // in BTC
  transactions: number;
}

export function RewardHistoryChart() {
  const [data, setData] = useState<RewardDataPoint[]>([]);
  const [isLoading, setIsLoading] = useState(true);
  const [timeRange, setTimeRange] = useState('month');
  const [showTooltip, setShowTooltip] = useState(false);
  const [tooltipData, setTooltipData] = useState<{
    x: number;
    y: number;
    data: RewardDataPoint | null;
  }>({
    x: 0,
    y: 0,
    data: null,
  });

  const chartRef = useRef<HTMLDivElement>(null);

  // Generate random reward history data
  useEffect(() => {
    setIsLoading(true);

    // Determine date range based on selected time range
    const endDate = new Date();
    const startDate = new Date();

    if (timeRange === 'week') {
      startDate.setDate(endDate.getDate() - 7);
    } else if (timeRange === 'month') {
      startDate.setDate(endDate.getDate() - 30);
    } else if (timeRange === 'year') {
      startDate.setDate(endDate.getDate() - 365);
    }

    // Generate data points
    const dataPoints: RewardDataPoint[] = [];
    const currentDate = new Date(startDate);

    // Base value and trend factors for more realistic data
    let baseValue = 0.002 + Math.random() * 0.001;
    let trendDirection = Math.random() > 0.5 ? 1 : -1;
    const volatility = 0.2;

    while (currentDate <= endDate) {
      // Create more realistic data with trends and volatility
      baseValue += trendDirection * (Math.random() * volatility * baseValue);

      // Occasionally change trend direction
      if (Math.random() < 0.1) {
        trendDirection *= -1;
      }

      // Ensure value stays within reasonable bounds
      baseValue = Math.max(0.0005, Math.min(0.004, baseValue));

      // Add some randomness to transactions
      const transactions = Math.floor(Math.random() * 5) + 1;

      dataPoints.push({
        date: currentDate.toISOString(),
        amount: baseValue,
        transactions,
      });

      // Increment date
      currentDate.setDate(currentDate.getDate() + 1);
    }

    // Simulate API delay
    setTimeout(() => {
      setData(dataPoints);
      setIsLoading(false);
    }, 1000);
  }, [timeRange]);

  // Handle mouse move for tooltip
  const handleMouseMove = (e: React.MouseEvent) => {
    if (!chartRef.current || data.length === 0) return;

    const rect = chartRef.current.getBoundingClientRect();
    const x = e.clientX - rect.left;
    const y = e.clientY - rect.top;

    // Calculate which data point is closest to the mouse
    const chartWidth = rect.width;
    const dataIndex = Math.min(
      Math.floor((x / chartWidth) * data.length),
      data.length - 1
    );

    if (dataIndex >= 0) {
      setTooltipData({
        x,
        y,
        data: data[dataIndex],
      });
      setShowTooltip(true);
    }
  };

  // Format date
  const formatDate = (dateString: string) => {
    const date = new Date(dateString);
    return date.toLocaleDateString('en-US', {
      month: 'short',
      day: 'numeric',
      year: 'numeric',
    });
  };

  // Convert BTC to mBTC
  const formatMBTC = (btc: number) => (btc * 1000).toFixed(2);

  // Calculate max value for scaling
  const maxValue = Math.max(...data.map((d) => d.amount)) * 1.2;

  return (
    <div className="relative border border-gray-800/50 rounded-xl bg-black/30 backdrop-blur-md overflow-hidden p-5">
      <div className="flex justify-between items-center mb-6">
        <h3 className="text-lg font-bold text-white flex items-center">
          <Calendar className="h-5 w-5 text-blue-400 mr-2" />
          Reward History
        </h3>

        <div className="flex items-center gap-2">
          <div className="bg-gray-900/50 rounded-lg p-1 flex">
            {['week', 'month', 'year'].map((range) => (
              <button
                key={range}
                className={`px-3 py-1 rounded-md text-sm font-medium transition-colors ${
                  timeRange === range
                    ? 'bg-blue-600/30 text-blue-200'
                    : 'text-gray-400 hover:text-white'
                }`}
                onClick={() => setTimeRange(range)}
              >
                {range.charAt(0).toUpperCase() + range.slice(1)}
              </button>
            ))}
          </div>

          <button className="bg-gray-900/50 p-2 rounded-lg text-gray-400 hover:text-white transition-colors">
            <Download className="h-4 w-4" />
          </button>

          <button className="bg-gray-900/50 p-2 rounded-lg text-gray-400 hover:text-white transition-colors">
            <Filter className="h-4 w-4" />
          </button>
        </div>
      </div>

      {isLoading ? (
        <div className="h-80 flex items-center justify-center">
          <div className="w-10 h-10 border-4 border-blue-500 border-t-transparent rounded-full animate-spin"></div>
        </div>
      ) : (
        <div
          className="h-80 relative"
          ref={chartRef}
          onMouseMove={handleMouseMove}
          onMouseLeave={() => setShowTooltip(false)}
        >
          {/* Chart grid */}
          <div className="absolute inset-0">
            {[0, 0.25, 0.5, 0.75, 1].map((ratio, i) => (
              <div
                key={i}
                className="absolute w-full h-px bg-gray-800/50"
                style={{ top: `${ratio * 100}%` }}
              />
            ))}
          </div>

          {/* Y-axis labels */}
          <div className="absolute left-0 top-0 bottom-0 w-16 flex flex-col justify-between text-gray-500 text-xs">
            {[1, 0.75, 0.5, 0.25, 0].map((ratio, i) => (
              <div key={i} className="flex items-center">
                <span>{formatMBTC(maxValue * ratio)} mBTC</span>
              </div>
            ))}
          </div>

          {/* Chart bars */}
          <div className="absolute left-16 right-0 top-0 bottom-0 flex items-end">
            {data.map((point, i) => {
              const height = (point.amount / maxValue) * 100;
              const isPositive =
                i > 0 ? point.amount >= data[i - 1].amount : true;

              return (
                <motion.div
                  key={i}
                  className="flex-1 mx-0.5 flex flex-col items-center justify-end"
                  initial={{ opacity: 0, y: 20 }}
                  animate={{ opacity: 1, y: 0 }}
                  transition={{ duration: 0.3, delay: i * 0.01 }}
                >
                  <motion.div
                    className={`w-full ${isPositive ? 'bg-blue-500/70' : 'bg-pink-500/70'} rounded-t-sm`}
                    style={{ height: `${height}%` }}
                    initial={{ height: 0 }}
                    animate={{ height: `${height}%` }}
                    transition={{ duration: 0.5, delay: 0.3 + i * 0.01 }}
                    whileHover={{ opacity: 0.8 }}
                  />

                  {/* Only show some X-axis labels to avoid overcrowding */}
                  {(i === 0 ||
                    i === Math.floor(data.length / 2) ||
                    i === data.length - 1) && (
                    <div className="absolute bottom-[-20px] text-gray-500 text-xs whitespace-nowrap">
                      {formatDate(point.date)}
                    </div>
                  )}
                </motion.div>
              );
            })}
          </div>

          {/* Tooltip */}
          {showTooltip && tooltipData.data && (
            <div
              className="absolute bg-gray-900/90 border border-gray-700 rounded-md p-2 text-xs text-white shadow-lg z-10 pointer-events-none"
              style={{
                left: `${tooltipData.x + 10}px`,
                top: `${tooltipData.y - 70}px`,
                transform:
                  tooltipData.x > chartRef.current!.clientWidth - 150
                    ? 'translateX(-100%)'
                    : 'none',
              }}
            >
              <div className="font-medium">
                {formatDate(tooltipData.data.date)}
              </div>
              <div className="text-blue-300 mt-1">
                Amount: {formatMBTC(tooltipData.data.amount)} mBTC
              </div>
              <div className="text-gray-300">
                Transactions: {tooltipData.data.transactions}
              </div>
            </div>
          )}
        </div>
      )}

      {/* Summary stats */}
      <div className="grid grid-cols-3 gap-4 mt-8">
        {[
          {
            label: 'Total Rewards',
            value: formatMBTC(
              data.reduce((sum, point) => sum + point.amount, 0)
            ),
            unit: 'mBTC',
            change: '+12.5%',
            isPositive: true,
          },
          {
            label: 'Average Reward',
            value: formatMBTC(
              data.reduce((sum, point) => sum + point.amount, 0) /
                (data.length || 1)
            ),
            unit: 'mBTC',
            change: '+3.2%',
            isPositive: true,
          },
          {
            label: 'Total Transactions',
            value: data.reduce((sum, point) => sum + point.transactions, 0),
            unit: '',
            change: '-2.1%',
            isPositive: false,
          },
        ].map((stat, i) => (
          <div key={i} className="bg-gray-900/50 rounded-lg p-3">
            <div className="text-gray-400 text-sm">{stat.label}</div>
            <div className="text-white text-xl font-bold mt-1">
              {stat.value}
              {stat.unit && (
                <span className="text-gray-400 text-sm ml-1">{stat.unit}</span>
              )}
            </div>
            <div
              className={`text-xs flex items-center mt-1 ${stat.isPositive ? 'text-blue-400' : 'text-pink-400'}`}
            >
              {stat.isPositive ? (
                <ArrowUpRight className="h-3 w-3 mr-1" />
              ) : (
                <ArrowDownRight className="h-3 w-3 mr-1" />
              )}
              {stat.change} from previous period
            </div>
          </div>
        ))}
      </div>
    </div>
  );
}
