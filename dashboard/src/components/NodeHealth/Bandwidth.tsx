import React, { useRef } from 'react';
import {
  LineChart,
  Line,
  XAxis,
  YAxis,
  Tooltip,
  CartesianGrid,
  ResponsiveContainer,
} from 'recharts';

import { BandwidthPanelProps } from './Types';
import { formatBytes } from './Utils';
import ActionIconButton from '../common/ActionIconButton';
import { downloadSvgFromContainer } from '../../utils/downloadSvg';

const BandwidthPanel: React.FC<BandwidthPanelProps> = ({
  bandwidthHistory,
}) => {
  const chartContainerRef = useRef<HTMLDivElement | null>(null);

  const handleDownload = () => {
    if (!chartContainerRef.current) return;
    downloadSvgFromContainer(chartContainerRef.current, 'bandwidth-usage');
  };

  if (bandwidthHistory.length === 0) {
    return (
      <div className="bg-[#1e1e1e] border border-gray-700 rounded-xl shadow-md p-4 text-center text-white">
        <p>No bandwidth data available.</p>
      </div>
    );
  }

  return (
    <div className="bg-[#1e1e1e] border border-gray-700 rounded-xl shadow-md p-4 relative">
      <div className="absolute right-3 top-3 z-10">
        <ActionIconButton
          onClick={handleDownload}
          icon={
            <svg
              xmlns="http://www.w3.org/2000/svg"
              viewBox="0 0 20 20"
              fill="currentColor"
            >
              <path d="M3 14.5A2.5 2.5 0 0 0 5.5 17h9a2.5 2.5 0 0 0 2.5-2.5V11a.75.75 0 0 0-1.5 0v3.5a1 1 0 0 1-1 1h-9a1 1 0 0 1-1-1V11a.75.75 0 0 0-1.5 0v3.5Z" />
              <path d="M10 2a.75.75 0 0 0-.75.75v8.19L7.53 9.22a.75.75 0 0 0-1.06 1.06l3 3a.75.75 0 0 0 1.06 0l3-3a.75.75 0 1 0-1.06-1.06L10.75 10.94V2.75A.75.75 0 0 0 10 2Z" />
            </svg>
          }
        />
      </div>
      <h3 className="text-lg font-semibold text-white mb-4 text-center">
        Real-Time Bandwidth Usage
      </h3>

      <div ref={chartContainerRef}>
        <ResponsiveContainer width="100%" height={350}>
          <LineChart
            data={bandwidthHistory}
            margin={{ top: 30, right: 30, left: 0, bottom: 5 }}
          >
            <CartesianGrid strokeDasharray="3 3" stroke="#444" />
            <XAxis
              dataKey="timestamp"
              tickFormatter={(ts) => new Date(ts).toLocaleTimeString()}
              stroke="#aaa"
            />
            <YAxis
              stroke="#aaa"
              tickFormatter={(value) => formatBytes(value)}
              allowDataOverflow
            />
            <Tooltip
              contentStyle={{ backgroundColor: '#222', borderColor: '#555' }}
              labelFormatter={(ts) => new Date(ts).toLocaleTimeString()}
              formatter={(value: number, name: string) => [
                formatBytes(value),
                name,
              ]}
            />
            <Line
              dataKey="bandwidthRecv"
              stroke="#4ade80"
              name="Bytes Received/sec"
            />
            <Line
              dataKey="bandwidthSent"
              stroke="#60a5fa"
              name="Bytes Sent/sec"
            />
          </LineChart>
        </ResponsiveContainer>
      </div>
    </div>
  );
};

export default BandwidthPanel;
