import React from 'react';
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

const BandwidthPanel: React.FC<BandwidthPanelProps> = ({
  bandwidthHistory,
}) => {
  if (bandwidthHistory.length === 0) {
    return (
      <div className="bg-[#1e1e1e] border border-gray-700 rounded-xl shadow-md p-4 text-center text-white">
        <p>No bandwidth data available.</p>
      </div>
    );
  }

  return (
    <div className="bg-[#1e1e1e] border border-gray-700 rounded-xl shadow-md p-4">
      <h3 className="text-lg font-semibold text-white mb-4 text-center">
        Real-Time Bandwidth Usage
      </h3>

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
  );
};

export default BandwidthPanel;
