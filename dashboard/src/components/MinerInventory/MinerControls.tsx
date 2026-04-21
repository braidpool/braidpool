import React from 'react';
import { MinerControlsProps } from './Types';

const MinerControls: React.FC<MinerControlsProps> = ({
  newMinerIP,
  setNewMinerIP,
  addMinerByIP,
  loading,
  lastUpdate,
}) => (
  <div className="mb-8 flex flex-col items-center gap-4">
    <div className="flex flex-wrap justify-center gap-2">
      <input
        type="text"
        value={newMinerIP}
        onChange={(e) => setNewMinerIP(e.target.value)}
        placeholder="Enter miner IP"
        aria-label="Miner IP"
        onKeyDown={(e) => e.key === 'Enter' && addMinerByIP()}
        className="rounded-lg border border-gray-700 bg-transparent px-3 py-1.5 text-sm text-white placeholder-gray-500 focus:outline-none focus:ring-1 focus:ring-indigo-500"
      />

      <button
        onClick={addMinerByIP}
        disabled={loading}
        className="rounded-lg bg-indigo-600 px-4 py-1.5 text-sm font-medium text-white transition-colors hover:bg-indigo-700 disabled:opacity-50"
      >
        {loading ? 'Adding...' : 'Add Miner'}
      </button>
    </div>

    <p className="text-center text-xs text-gray-500">
      {lastUpdate
        ? `Updated ${lastUpdate.toLocaleTimeString()}`
        : 'Never updated'}
    </p>
  </div>
);

export default MinerControls;
