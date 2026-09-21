import React from 'react';
import { MinerControlsProps } from './Types';

const MinerControls: React.FC<MinerControlsProps> = ({
  loading,
  lastUpdate,
  wsConnected,
}) => (
  <div className="mt-4 mb-8 flex items-center justify-center gap-4 text-sm text-gray-400">
    <span className="flex items-center gap-1.5">
      <span
        className={`inline-block w-2 h-2 rounded-full ${
          wsConnected ? 'bg-emerald-400' : 'bg-gray-500'
        }`}
      />
      {wsConnected ? 'Live' : 'Polling'}
    </span>
    {loading && (
      <span className="flex items-center gap-1.5">
        <span className="inline-block w-2 h-2 rounded-full bg-indigo-400 animate-pulse" />
        Refreshing…
      </span>
    )}
    <span>
      {lastUpdate
        ? `Last update: ${lastUpdate.toLocaleString()}`
        : 'Waiting for first update…'}
    </span>
    <span className="text-gray-600">· Auto-scanning LAN</span>
  </div>
);

export default MinerControls;
