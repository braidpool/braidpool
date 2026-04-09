import React from 'react';
import { MinerControlsProps } from './Types';

const MinerControls: React.FC<MinerControlsProps> = ({
  newMinerIP,
  setNewMinerIP,
  addMinerByIP,
  loading,
  lastUpdate,
}) => (
  <div className="mt-6 relative flex items-center w-full gap-2 mb-12">
    <div className="absolute left-1/2 transform -translate-x-1/2 flex gap-2">
      <input
        type="text"
        value={newMinerIP}
        onChange={(e) => setNewMinerIP(e.target.value)}
        placeholder="Enter Miner IP"
        aria-label="Miner IP"
        className="w-64 px-3 py-2 text-sm text-center border border-gray-600 bg-gray-800 rounded text-white placeholder-gray-400 focus:outline-none focus:ring-1 focus:ring-gray-500"
        onKeyDown={(e) => e.key === 'Enter' && addMinerByIP()}
      />
      <button
        onClick={addMinerByIP}
        disabled={loading}
        className="px-4 py-2 text-sm text-white rounded bg-gray-800 cursor-pointer"
      >
        {loading ? 'Adding...' : 'Add Miner'}
      </button>
    </div>
    <div className="ml-auto flex items-center gap-2 text-sm text-gray-400">
      <div>
        {lastUpdate
          ? `Last update: ${lastUpdate.toLocaleString()}`
          : 'Never updated'}
      </div>
    </div>
  </div>
);

export default MinerControls;
