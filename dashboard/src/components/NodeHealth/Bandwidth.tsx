import React from 'react';
import { LineChart, Line, XAxis, YAxis, CartesianGrid, Tooltip, Legend, ResponsiveContainer } from 'recharts';
import { BandwidthPanelProps, BandwidthHistoryPoint } from './Types';

const BandwidthPanel: React.FC<BandwidthPanelProps> = ({ nettotals, bandwidthHistory }) => {
  const chartData = bandwidthHistory.map((point: BandwidthHistoryPoint) => ({
    time: new Date(point.timestamp).toLocaleTimeString(),
    'Received (KB/s)': Number((point.recvRate / 1024).toFixed(2)),
    'Sent (KB/s)': Number((point.sentRate / 1024).toFixed(2))
  }));

  const currentRecvRate = bandwidthHistory.length > 0 
    ? bandwidthHistory[bandwidthHistory.length - 1].recvRate 
    : 0;
  const currentSentRate = bandwidthHistory.length > 0 
    ? bandwidthHistory[bandwidthHistory.length - 1].sentRate 
    : 0;

  return (
    <div className="space-y-6">
      {/* Current Bandwidth Stats */}
      <div className="grid grid-cols-1 md:grid-cols-2 gap-4">
        <div className="bg-[#1c1c1c] border border-gray-700 rounded-xl p-4">
          <h3 className="text-white font-semibold mb-2">Current Bandwidth</h3>
          <div className="space-y-2">
            <div className="flex justify-between">
              <span className="text-gray-500">Download Rate:</span>
              <span className="text-green-500">{(currentRecvRate / 1024).toFixed(2)} KB/s</span>
            </div>
            <div className="flex justify-between">
              <span className="text-gray-500">Upload Rate:</span>
              <span className="text-blue-500">{(currentSentRate / 1024).toFixed(2)} KB/s</span>
            </div>
          </div>
        </div>

        <div className="bg-[#1c1c1c] border border-gray-700 rounded-xl p-4">
          <h3 className="text-white font-semibold mb-2">Total Bandwidth</h3>
          <div className="space-y-2">
            <div className="flex justify-between">
              <span className="text-gray-500">Total Received:</span>
              <span className="text-white">{(nettotals.totalbytesrecv / (1024 * 1024 * 1024)).toFixed(2)} GB</span>
            </div>
            <div className="flex justify-between">
              <span className="text-gray-500">Total Sent:</span>
              <span className="text-white">{(nettotals.totalbytessent / (1024 * 1024 * 1024)).toFixed(2)} GB</span>
            </div>
          </div>
        </div>
      </div>

      {/* Network Activity Summary */}
      <div className="bg-[#1c1c1c] border border-gray-700 rounded-xl p-4">
        <h3 className="text-white font-semibold mb-2">Network Activity Summary</h3>
        <div className="grid grid-cols-2 md:grid-cols-4 gap-4 text-sm">
          <div className="text-center">
            <p className="text-gray-500">Data Points</p>
            <p className="text-white font-bold">{bandwidthHistory.length}</p>
          </div>
          <div className="text-center">
            <p className="text-gray-500">Avg Download</p>
            <p className="text-green-500 font-bold">
              {bandwidthHistory.length > 0 
                ? (bandwidthHistory.reduce((sum, point) => sum + point.recvRate, 0) / bandwidthHistory.length / 1024).toFixed(2)
                : '0.00'} KB/s
            </p>
          </div>
          <div className="text-center">
            <p className="text-gray-500">Avg Upload</p>
            <p className="text-blue-500 font-bold">
              {bandwidthHistory.length > 0 
                ? (bandwidthHistory.reduce((sum, point) => sum + point.sentRate, 0) / bandwidthHistory.length / 1024).toFixed(2)
                : '0.00'} KB/s
            </p>
          </div>
          <div className="text-center">
            <p className="text-gray-500">Peak Download</p>
            <p className="text-green-400 font-bold">
              {bandwidthHistory.length > 0 
                ? (Math.max(...bandwidthHistory.map(p => p.recvRate)) / 1024).toFixed(2)
                : '0.00'} KB/s
            </p>
          </div>
        </div>
      </div>

      {/* Bandwidth Chart */}
      <div className="bg-[#1c1c1c] border border-gray-700 rounded-xl p-4">
        <h3 className="text-white font-semibold mb-4">Bandwidth Usage Over Time</h3>
        {bandwidthHistory.length > 0 ? (
          <ResponsiveContainer width="100%" height={300}>
            <LineChart data={chartData}>
              <CartesianGrid strokeDasharray="3 3" stroke="#374151" />
              <XAxis 
                dataKey="time" 
                stroke="#9CA3AF" 
                fontSize={12}
                tick={{ fill: '#9CA3AF' }}
              />
              <YAxis 
                stroke="#9CA3AF" 
                fontSize={12}
                tick={{ fill: '#9CA3AF' }}
                label={{ value: 'KB/s', angle: -90, position: 'insideLeft', style: { textAnchor: 'middle', fill: '#9CA3AF' } }}
              />
              <Tooltip 
                contentStyle={{ 
                  backgroundColor: '#1c1c1c', 
                  border: '1px solid #374151',
                  borderRadius: '8px',
                  color: '#fff'
                }}
                labelStyle={{ color: '#9CA3AF' }}
              />
              <Legend />
              <Line 
                type="monotone" 
                dataKey="Received (KB/s)" 
                stroke="#10B981" 
                strokeWidth={2}
                dot={false}
                activeDot={{ r: 4, fill: '#10B981' }}
              />
              <Line 
                type="monotone" 
                dataKey="Sent (KB/s)" 
                stroke="#3B82F6" 
                strokeWidth={2}
                dot={false}
                activeDot={{ r: 4, fill: '#3B82F6' }}
              />
            </LineChart>
          </ResponsiveContainer>
        ) : (
          <div className="h-[300px] flex items-center justify-center">
            <p className="text-gray-500">No bandwidth data available yet. Waiting for data...</p>
          </div>
        )}
      </div>

    
    </div>
  );
};

export default BandwidthPanel;