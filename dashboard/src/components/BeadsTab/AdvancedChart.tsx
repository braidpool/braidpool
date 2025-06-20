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
import { Props } from './lib/types';
import { useState, useRef } from 'react';
export default function AdvancedChart({
  data,
  height = 300,
  isHovered = false,
  showControls = true,
  isLoading = false,
  comparisonData,
  tooltipFormatter,
  primaryLabel='primary'

  
}: Props) {
  const [isZoomed, setIsZoomed] = useState(false);
  const [isRefreshing, setIsRefreshing] = useState(false);

  const handleRefresh = () => {
    setIsRefreshing(true);
    setTimeout(() => {
      setIsRefreshing(false);
    }, 1500);
  };
const chartRef = useRef<HTMLDivElement>(null);

 const handleExport = () => {
  const svg = chartRef.current?.querySelector('svg');
  if (!svg) return;
  const serializer = new XMLSerializer();
  const source = serializer.serializeToString(svg);
  const blob = new Blob([source], { type: 'image/svg+xml' });
  const url = URL.createObjectURL(blob);
  const link = document.createElement('a');
  link.href = url;
  link.download = `chart-${Date.now()}.svg`;
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
        <div className="absolute top-0 right-0 flex space-x-2 z-10 p-2 ">
          <button
            className="bg-gray-800/70  p-1.5 rounded-md text-gray-300 hover:text-white transition-transform duration-200 hover:scale-110 active:scale-95"
            onClick={() => setIsZoomed(!isZoomed)}
            title="Toggle zoom"
          >
            <Maximize2 size={16} />
          </button>
          <button
            className={`bg-gray-800/70 p-1.5 rounded-md text-gray-300 hover:text-white transition-transform duration-200 hover:scale-110 active:scale-95 ${
              isRefreshing ? 'cursor-not-allowed opacity-60' : ''
            }`}
            onClick={handleRefresh}
            disabled={isRefreshing}
            title="Refresh chart"
          >
            <RefreshCw
              size={16}
              className={isRefreshing ? 'animate-spin' : ''}
            />
          </button>
          <button
            className="bg-gray-800/70 p-1.5 rounded-md text-gray-300 hover:text-white transition-transform duration-200 hover:scale-110 active:scale-95"
            onClick={handleExport}
            title="Export chart"
          >
            <Download size={16} />
          </button>
        </div>
      )}

      <div ref={chartRef} className="w-full h-full pt-8">
        <ResponsiveContainer width="100%" height={chartHeight}>
          <LineChart data={data}>
            <defs>
              <linearGradient id="colorValue" x1="0" y1="0" x2="0" y2="1">
                <stop offset="5%" stopColor="#3b82f6" stopOpacity={0.8} />
                <stop offset="95%" stopColor="#3b82f6" stopOpacity={0} />
              </linearGradient>
              {comparisonData && (
                <linearGradient
                  id="colorComparison"
                  x1="0"
                  y1="0"
                  x2="0"
                  y2="1"
                >
                  <stop offset="5%" stopColor="#10b981" stopOpacity={0.5} />
                  <stop offset="95%" stopColor="#10b981" stopOpacity={0} />
                </linearGradient>
              )}
            </defs>

            <CartesianGrid strokeDasharray="3 3" stroke="#4b5563" />
            <XAxis
              dataKey="label"
              stroke="#ffffff"
              tickFormatter={(_, index) => {
                const dataPoint = data[index];
                if (dataPoint && dataPoint.date) {
                  const d = new Date(dataPoint.date);
                  return d.toLocaleDateString('en-US', {
                    month: 'short',
                    day: 'numeric',
                  });
                }
                return '';
              }}
            />
            <YAxis stroke="#ffffff" />
           <Tooltip
  contentStyle={{
    backgroundColor: '#1f2937',
    borderColor: '#3b82f6',
    borderRadius: 8,
  }}
  labelStyle={{ color: '#fff' }}
  itemStyle={{ color: '#fff' }}
  formatter={tooltipFormatter || ((value: number, name: string) => [`${value}`, name])}

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
                 
                />
                <Area
                  type="monotone"
                  dataKey="value"
                  
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
              name={primaryLabel}

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
