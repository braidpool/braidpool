import React from 'react';
import { MinerDashboardHeaderProps } from './Types';

const MinerDashboardHeader: React.FC<MinerDashboardHeaderProps> = ({
  totalMiners,
  totalHashrate,
  totalPower,
  avgEfficiency,
}) => (
  <div className="grid grid-cols-2 lg:grid-cols-4 gap-4 mb-8">
    {[
      { label: 'Total miners', value: totalMiners },
      { label: 'Total hashrate', value: `${totalHashrate.toFixed(3)} TH/s` },
      { label: 'Total power', value: `${totalPower} W` },
      { label: 'Avg efficiency', value: `${avgEfficiency.toFixed(1)} W/TH` },
    ].map(({ label, value }) => (
      <div key={label} className="border border-gray-700 rounded-xl p-4">
        <p className="text-xs uppercase tracking-widest text-gray-400 mb-1">
          {label}
        </p>
        <p className="text-sm font-medium text-gray-200">{value}</p>
      </div>
    ))}
  </div>
);

export default MinerDashboardHeader;
