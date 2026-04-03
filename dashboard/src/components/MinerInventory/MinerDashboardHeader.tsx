import React from 'react';
import { MinerDashboardHeaderProps } from './Types';

const MinerDashboardHeader: React.FC<MinerDashboardHeaderProps> = ({
  totalMiners,
  totalHashrate,
  totalPower,
  avgEfficiency,
}) => (
  <div className="grid grid-cols-2 lg:grid-cols-4 gap-5 text-sm max-w-4xl mx-auto">
    <div className="px-2 py-1 rounded-md border border-gray-600  text-gray-400 text-center">
      <div className="font-medium text-sm">Total Miners</div>
      <div className="text-sm text-white mt-1">{totalMiners}</div>
    </div>
    <div className="px-2 py-1 rounded-md border border-gray-600 text-gray-400 text-center">
      <div className="font-medium text-sm">Total Hashrate</div>
      <div className="text-sm text-white mt-1">
        {totalHashrate.toFixed(3)} TH/s
      </div>
    </div>
    <div className="px-2 py-1 rounded-md border border-gray-600 text-gray-400 text-center">
      <div className="font-medium text-sm">Total Power</div>
      <div className="text-sm text-white mt-1">{totalPower}W</div>
    </div>
    <div className="px-2 py-1 rounded-md border border-gray-600 text-gray-400 text-center">
      <div className="font-medium text-sm">Avg Efficiency</div>
      <div className="text-sm text-white mt-1">
        {avgEfficiency.toFixed(1)} W/TH
      </div>
    </div>
  </div>
);

export default MinerDashboardHeader;
