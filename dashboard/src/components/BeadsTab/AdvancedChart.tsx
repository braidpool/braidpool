import {
  LineChart,
  Line,
  XAxis,
  YAxis,
  CartesianGrid,
  Tooltip,
  ResponsiveContainer,
  Area,
  
} from 'recharts';
import { Maximize2, RefreshCw, Download } from 'lucide-react';
import { useState } from 'react';
import { motion } from 'framer-motion';

type TrendType = 'up' | 'down' | 'neutral';

interface ChartDataPoint {
  value: number;
  label: string;
  date: Date;
  formattedDate?: string;
  trend?: TrendType;
}

interface Props {
  data: ChartDataPoint[];
  height?: number;
  isHovered?: boolean;
  showControls?: boolean;
  isLoading?: boolean;
  comparisonData?: ChartDataPoint[];
  comparisonLabel?: string;
  timeRange: string;
}

export default function AdvancedChart({
  data,
  height = 300,
  isHovered = false,
  showControls = true,
  isLoading = false,
  comparisonData,
  comparisonLabel = 'Comparison',
}: Props) {
  const [isZoomed, setIsZoomed] = useState(false);
  const [isRefreshing, setIsRefreshing] = useState(false);

  const handleRefresh = () => {
    setIsRefreshing(true);
    setTimeout(() => {
      setIsRefreshing(false);
      
    }, 1500);
  };

  const handleExport = () => {
    const svg = document.querySelector('svg');
    if (!svg) return;
    const serializer = new XMLSerializer();
    const source = serializer.serializeToString(svg);
    const blob = new Blob([source], { type: 'image/svg+xml' });
    const url = URL.createObjectURL(blob);
    const link = document.createElement('a');
    link.href = url;
    link.download = 'chart.svg';
    link.click();
  };

  const chartHeight = isZoomed ? 400 : height;

  return (
    <div className="relative w-full h-full">
      {isLoading && (
        <div className="absolute inset-0 bg-black/30 backdrop-blur-sm flex items-center justify-center z-20">
          <div className="flex flex-col items-center">
            <div className="w-10 h-10 border-4 border-blue-500 border-t-transparent rounded-full animate-spin mb-2" />
            <p className="text-blue-300">Loading chart data...</p>
          </div>
        </div>
      )}

      {showControls && (
        <div className="absolute top-0 right-0 flex space-x-2 z-10 p-2">
          <motion.button
            className="bg-gray-800/70 p-1.5 rounded-md text-gray-300 hover:text-white"
            whileHover={{ scale: 1.1 }}
            whileTap={{ scale: 0.95 }}
            onClick={() => setIsZoomed(!isZoomed)}
            title="Toggle zoom"
          >
            <Maximize2 size={16} />
          </motion.button>
          <motion.button
            className="bg-gray-800/70 p-1.5 rounded-md text-gray-300 hover:text-white"
            whileHover={{ scale: 1.1 }}
            whileTap={{ scale: 0.95 }}
            onClick={handleRefresh}
            disabled={isRefreshing}
            title="Refresh chart"
          >
            <RefreshCw size={16} className={isRefreshing ? 'animate-spin' : ''} />
          </motion.button>
          <motion.button
            className="bg-gray-800/70 p-1.5 rounded-md text-gray-300 hover:text-white"
            whileHover={{ scale: 1.1 }}
            whileTap={{ scale: 0.95 }}
            onClick={handleExport}
            title="Export chart"
          >
            <Download size={16} />
          </motion.button>
        </div>
      )}

      <div className="w-full h-full pt-8">
        <ResponsiveContainer width="100%" height={chartHeight}>
          <LineChart data={data}>
            <defs>
              <linearGradient id="colorValue" x1="0" y1="0" x2="0" y2="1">
                <stop offset="5%" stopColor="#3b82f6" stopOpacity={0.8} />
                <stop offset="95%" stopColor="#3b82f6" stopOpacity={0} />
              </linearGradient>
              <linearGradient id="colorComparison" x1="0" y1="0" x2="0" y2="1">
                <stop offset="5%" stopColor="#10b981" stopOpacity={0.6} />
                <stop offset="95%" stopColor="#10b981" stopOpacity={0} />
              </linearGradient>
            </defs>

            <CartesianGrid strokeDasharray="3 3" stroke="#4b5563" />
            <XAxis dataKey="label" stroke="#ffffff" />
            <YAxis stroke="#ffffff" />
            <Tooltip
              contentStyle={{
                backgroundColor: '#1f2937',
                borderColor: '#3b82f6',
                borderRadius: 8,
              }}
              labelStyle={{ color: '#fff' }}
              itemStyle={{ color: '#fff' }}
            />

            {comparisonData && (
              <>
                <Line
                  type="monotone"
                  dataKey="value"
                  data={comparisonData}
                  stroke="#10b981"
                  strokeWidth={2}
                  dot={false}
                  name={comparisonLabel}
                />
                <Area
                  type="monotone"
                  dataKey="value"
                  data={comparisonData}
                  
                  fillOpacity={1}
                  fill="url(#colorComparison)"
                />
              </>
            )}

            <Line
              type="monotone"
              dataKey="value"
              stroke="#3b82f6"
              strokeWidth={3}
              dot={isHovered}
              name="Primary"
            />
            <Area
              type="monotone"
              dataKey="value"
              
              fillOpacity={0.7}
              fill="url(#colorValue)"
            />
          </LineChart>
        </ResponsiveContainer>
      </div>
    </div>
  );
}
