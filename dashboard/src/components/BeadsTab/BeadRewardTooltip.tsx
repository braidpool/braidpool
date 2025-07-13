import { useState } from 'react';
import { Bitcoin } from 'lucide-react';

import { BeadRewardTooltipProps } from './lib/Types';

export function BeadRewardTooltip({ reward }: BeadRewardTooltipProps) {
  const [showTooltip, setShowTooltip] = useState(false);

  // Convert BTC to mBTC
  const mBTC = reward * 1000;

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
      opacity-100 scale-100
    `}
        >
          <span>{mBTC.toFixed(2)} mBTC</span>
        </div>
      )}
    </div>
  );
}
