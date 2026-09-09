import React from 'react';

import { BandwidthPanelProps } from './Types';
import { formatBytes } from './Utils';
import MultiLineChart from '../common/charts/MultiLineChart';

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
    <MultiLineChart
      data={bandwidthHistory}
      xAxisKey="timestamp"
      series={[
        {
          dataKey: 'bandwidthRecv',
          label: 'Bytes Received/sec',
          color: '#4ade80',
        },
        {
          dataKey: 'bandwidthSent',
          label: 'Bytes Sent/sec',
          color: '#60a5fa',
        },
      ]}
      title="Real-Time Bandwidth Usage"
      downloadFileName="bandwidth-usage"
      showLegend={false}
      xAxisTickFormatter={(timestamp) =>
        new Date(Number(timestamp)).toLocaleTimeString()
      }
      yAxisTickFormatter={(value) => formatBytes(value)}
      tooltipLabelFormatter={(timestamp) =>
        new Date(Number(timestamp)).toLocaleTimeString()
      }
      tooltipValueFormatter={(value) => formatBytes(Number(value))}
    />
  );
};

export default BandwidthPanel;
