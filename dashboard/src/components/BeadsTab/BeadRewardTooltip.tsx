import { useState } from 'react';
import { Bitcoin } from 'lucide-react';

import { BeadRewardTooltipProps } from './lib/types';

export function BeadRewardTooltip({ reward }: BeadRewardTooltipProps) {
  const [showTooltip, setShowTooltip] = useState(false);

  // Convert BTC to mBTC
  const mBTC = reward * 1000;

  // Calculate USD value (assuming 1 BTC = $60,000)
  const usdValue = reward * 60000;

  return (
    <div className="relative inline-block">
      <div
        className="flex items-center cursor-pointer transition-transform hover:scale-105"
        onMouseEnter={() => setShowTooltip(true)}
        onMouseLeave={() => setShowTooltip(false)}
        onClick={() => setShowTooltip(!showTooltip)} // For mobile support
      >
        <Bitcoin className="h-4 w-4 text-amber-400 mr-1" />
        <span>{mBTC.toFixed(2)} mBTC</span>
      </div>

      {showTooltip && (
        <div
          className={`
            absolute z-50 top-full left-1/2 transform -translate-x-1/2 translate-y-2 w-48 
            bg-gray-900/95 border border-gray-700 rounded-lg shadow-xl p-3
            transition-all duration-200
            ${showTooltip ? 'opacity-100 scale-100' : 'opacity-0 scale-90 -translate-y-1'}
          `}
        >
          <div className="flex justify-between text-xs text-gray-400 mb-1">
            <span>BTC Value:</span>
            <span className="text-white">{reward.toFixed(8)} BTC</span>
          </div>
          <div className="flex justify-between text-xs text-gray-400">
            <span>USD Value:</span>
            <span className="text-white">${usdValue.toFixed(2)}</span>
          </div>

          {/* Arrow pointing up */}
          <div className="absolute top-[-6px] left-1/2 transform -translate-x-1/2 w-3 h-3 rotate-45 bg-gray-900 border-l border-t border-gray-700"></div>
        </div>
      )}
    </div>
  );
}
