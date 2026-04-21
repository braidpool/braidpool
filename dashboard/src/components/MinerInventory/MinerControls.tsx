import React from 'react';
import { MinerControlsProps } from './Types';

const MinerControls: React.FC<MinerControlsProps> = ({
  newMinerIP,
  setNewMinerIP,
  addMinerByIP,
  loading,
  lastUpdate,
}) => (
  <div className="flex items-center justify-between gap-4 mb-8">
    <div className="flex gap-2">
      <input
        type="text"
        value={newMinerIP}
        onChange={(e) => setNewMinerIP(e.target.value)}
        placeholder="Enter miner IP"
        aria-label="Miner IP"
        onKeyDown={(e) => e.key === 'Enter' && addMinerByIP()}
        className="px-3 py-1.5 text-sm border border-gray-700 bg-transparent rounded-lg text-white placeholder-gray-500 focus:outline-none focus:ring-1 focus:ring-indigo-500"
      />
      <button
        onClick={addMinerByIP}
        disabled={loading}
        className="px-4 py-1.5 text-sm font-medium rounded-lg bg-indigo-600 text-white hover:bg-indigo-700 disabled:opacity-50 transition-colors"
      >
        {loading ? 'Adding...' : 'Add Miner'}
      </button>
    </div>
    <p className="text-xs text-gray-500">
      {lastUpdate ? `Updated ${lastUpdate.toLocaleTimeString()}` : 'Never updated'}
    </p>
  </div>
);

export default MinerControls;