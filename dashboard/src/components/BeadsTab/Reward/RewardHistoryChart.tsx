'use client';

import {ResponsiveContainer,BarChart,Bar,XAxis,YAxis,Tooltip,CartesianGrid} from 'recharts';
import {Calendar,Download,Filter,ArrowUpRight,ArrowDownRight,} from 'lucide-react';
import { useEffect, useState } from 'react';

type TIME_RANGES = 'week' | 'month' | 'year';

interface RewardDataPoint {
  date: string;
  amount: number;
  transactions: number;
}

export function RewardHistoryChart() {
  const [data, setData] = useState<RewardDataPoint[]>([]);
  const [isLoading, setIsLoading] = useState(true);
  const [timeRange, setTimeRange] = useState<TIME_RANGES>('month');

  useEffect(() => {
    setIsLoading(true);
    const endDate = new Date();
    const startDate = new Date();

    if (timeRange === 'week') startDate.setDate(endDate.getDate() - 7);
    else if (timeRange === 'month') startDate.setDate(endDate.getDate() - 30);
    else if (timeRange === 'year') startDate.setDate(endDate.getDate() - 365);

    const dataPoints: RewardDataPoint[] = [];
    const currentDate = new Date(startDate);
    let baseValue = 0.002 + Math.random() * 0.001;
    let trendDirection = Math.random() > 0.5 ? 1 : -1;
    const volatility = 0.2;

    while (currentDate <= endDate) {
      baseValue += trendDirection * (Math.random() * volatility * baseValue);
      if (Math.random() < 0.1) trendDirection *= -1;
      baseValue = Math.max(0.0005, Math.min(0.004, baseValue));

      dataPoints.push({
        date: currentDate.toLocaleDateString('en-US', {
          month: 'short',
          day: 'numeric',
        }),
        amount: baseValue,
        transactions: Math.floor(Math.random() * 5) + 1,
      });

      currentDate.setDate(currentDate.getDate() + 1);
    }

    setTimeout(() => {
      setData(dataPoints);
      setIsLoading(false);
    }, 800);
  }, [timeRange]);

  const formatMBTC = (btc: number) => (btc * 1000).toFixed(2);

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
                onClick={() => setTimeRange(range as TIME_RANGES)}
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
        <ResponsiveContainer width="100%" height={320}>
          <BarChart data={data}>
            <CartesianGrid stroke="#2d2d2d" vertical={false} />
            <XAxis dataKey="date" tick={{ fill: '#888' }} />
            <YAxis tick={{ fill: '#888' }} />
            <Tooltip
              contentStyle={{ backgroundColor: '#1f1f1f', borderColor: '#444' }}
              labelStyle={{ color: '#ddd' }}
              formatter={(value: number) => [`${formatMBTC(value)} mBTC`, 'Amount']}
            />
            <Bar
              dataKey="amount"
              fill="#273F4F"
              animationDuration={800}
              radius={[4, 4, 0, 0]}
            />
          </BarChart>
        </ResponsiveContainer>
      )}

      {/* Summary Stats */}
      <div className="grid grid-cols-3 gap-4 mt-8">
        {[
          {
            label: 'Total Rewards',
            value: formatMBTC(data.reduce((sum, p) => sum + p.amount, 0)),
            unit: 'mBTC',
            change: '+12.5%',
            isPositive: true,
          },
          {
            label: 'Average Reward',
            value: formatMBTC(
              data.reduce((sum, p) => sum + p.amount, 0) / (data.length || 1)
            ),
            unit: 'mBTC',
            change: '+3.2%',
            isPositive: true,
          },
          {
            label: 'Total Transactions',
            value: data.reduce((sum, p) => sum + p.transactions, 0),
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
              className={`text-xs flex items-center mt-1 ${
                stat.isPositive ? 'text-blue-400' : 'text-pink-400'
              }`}
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
