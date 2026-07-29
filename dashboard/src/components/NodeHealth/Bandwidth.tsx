import React, { useRef, useState, useMemo } from 'react';
import {
  LineChart,
  Line,
  XAxis,
  YAxis,
  Tooltip,
  CartesianGrid,
  ResponsiveContainer,
} from 'recharts';
import { Activity, Download } from 'lucide-react';

import { BandwidthPanelProps } from './Types';
import { formatBytes } from './Utils';
import { downloadSvgFromContainer } from '../../utils/downloadSvg';
import { TimeRangeLabel } from './Types';
import { TIME_RANGES } from './Constants';

const BandwidthPanel: React.FC<BandwidthPanelProps> = ({
  bandwidthHistory,
}) => {
  const chartContainerRef = useRef<HTMLDivElement | null>(null);
  const [timeRange, setTimeRange] = useState<TimeRangeLabel>('1m');

  const handleDownload = () => {
    if (!chartContainerRef.current) return;
    downloadSvgFromContainer(chartContainerRef.current, 'bandwidth-usage');
  };

  const filteredHistory = useMemo(() => {
    if (bandwidthHistory.length === 0) return [];
    const selected = TIME_RANGES.find((r) => r.label === timeRange);
    if (!selected) return bandwidthHistory;
    const cutoff = Date.now() - selected.seconds * 1000;
    const filtered = bandwidthHistory.filter((p) => p.timestamp >= cutoff);
    return filtered.length > 0 ? filtered : bandwidthHistory;
  }, [bandwidthHistory, timeRange]);

  if (bandwidthHistory.length === 0) {
    return (
      <div className="bg-[#1e1e1e] border border-gray-700 rounded-xl shadow-md p-4 text-center text-white">
        <p>No bandwidth data available.</p>
      </div>
    );
  }

  return (
    <div className="bg-[#1e1e1e] border border-gray-700 rounded-lg p-5">
      {/* Header */}
      <div className="flex items-center justify-between mb-5">
        <div className="flex items-center gap-2">
          <Activity className="w-4 h-4 text-blue-400" />
          <h3 className="text-base font-semibold text-white">
            Real-Time Bandwidth Usage
          </h3>
        </div>
        <div className="flex items-center gap-2">
          <div className="flex items-center gap-0.5 bg-gray-800 rounded-md p-0.5">
            {TIME_RANGES.map(({ label }) => (
              <button
                key={label}
                onClick={() => setTimeRange(label)}
                className={`px-2 py-0.5 rounded text-xs font-medium transition-colors ${
                  timeRange === label
                    ? 'bg-[#1e1e1e] text-white border border-gray-600'
                    : 'text-gray-500 hover:text-gray-300'
                }`}
              >
                {label}
              </button>
            ))}
          </div>
          <button
            onClick={handleDownload}
            className="p-1.5 rounded text-gray-500 hover:text-gray-300 hover:bg-gray-800 transition-colors"
            aria-label="Download chart"
          >
            <Download className="w-4.5 h-4.5" />
          </button>
        </div>
      </div>

      <div ref={chartContainerRef}>
        <ResponsiveContainer width="100%" height={300}>
          <LineChart
            data={filteredHistory}
            margin={{ top: 10, right: 10, left: 0, bottom: 5 }}
          >
            <CartesianGrid strokeDasharray="3 3" stroke="#444" />
            <XAxis
              dataKey="timestamp"
              tickFormatter={(ts) => new Date(ts).toLocaleTimeString()}
              stroke="#aaa"
              tickMargin={10}
              tick={{ fill: '#777', fontSize: 15 }}
              tickLine={false}
              axisLine={{ stroke: '#333' }}
            />
            <YAxis
              stroke="#aaa"
              tickFormatter={(value) => formatBytes(value)}
              tick={{ fill: '#777', fontSize: 15 }}
              tickLine={false}
              axisLine={false}
              width={45}
            />
            <Tooltip
              contentStyle={{
                backgroundColor: '#1a1a1a',
                borderColor: '#333',
                borderRadius: '6px',
                fontSize: '12px',
              }}
              labelFormatter={(ts) => new Date(ts).toLocaleTimeString()}
              formatter={(value: number, name: string) => [
                formatBytes(value),
                name,
              ]}
            />
            <Line
              dataKey="bandwidthRecv"
              stroke="#4ade80"
              name="↓ Received/s"
              strokeWidth={1.5}
              dot={{ r: 2.5, fill: '#4ade80', strokeWidth: 0 }}
              activeDot={{ r: 4 }}
            />
            <Line
              dataKey="bandwidthSent"
              stroke="#60a5fa"
              name="↑ Sent/s"
              strokeWidth={1.5}
              dot={{ r: 2.5, fill: '#60a5fa', strokeWidth: 0 }}
              activeDot={{ r: 4 }}
            />
          </LineChart>
        </ResponsiveContainer>
      </div>
    </div>
  );
};

export default BandwidthPanel;
