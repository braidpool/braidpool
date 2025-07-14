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
  const filteredData = bandwidthHistory.length > 1 ? bandwidthHistory : [];

  return (
    <div className="bg-[#1c1c1c] border border-gray-700 rounded-xl shadow-md p-4">
      <h3 className="text-lg font-semibold text-white mb-4 text-center">
        Real-Time Bandwidth Usage (bytes/sec)
      </h3>

      <ResponsiveContainer width="100%" height={300}>
        <LineChart data={filteredData}>
          <CartesianGrid strokeDasharray="3 3" stroke="#444" />
          <XAxis
            dataKey="timestamp"
            tickFormatter={(ts) => new Date(ts).toLocaleTimeString()}
            stroke="#aaa"
          />
          <YAxis stroke="#aaa" tickFormatter={(value) => formatBytes(value)} />
          <Tooltip
            contentStyle={{ backgroundColor: '#222', borderColor: '#555' }}
            labelFormatter={(ts) => new Date(ts).toLocaleTimeString()}
            formatter={(value: number, name: string) => [
              formatBytes(value),
              name,
            ]}
          />
          <Line
            dataKey="totalbytesrecv"
            stroke="#4ade80"
            name="Bytes Received"
          />
          <Line dataKey="totalbytessent" stroke="#60a5fa" name="Bytes Sent" />
        </LineChart>
      </ResponsiveContainer>
    </div>
  );
};

export default BandwidthPanel;
