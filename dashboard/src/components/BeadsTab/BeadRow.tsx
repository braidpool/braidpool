import React, { useState } from 'react';
import { ChevronDown } from 'lucide-react';
import TransactionList from './TransactionList';
import { shortenHash } from './lib/utils/utils';
import type { BeadRowProps } from './lib/types';
import { BeadRewardTooltip } from './BeadRewardTooltip';
import { formatWork } from './lib/utils/utils';

export default function BeadRow({
  bead,
  isExpanded,
  onToggle,
  transactions,
  onParentClick,
}: BeadRowProps) {
  const { value: formattedWork, unit: workUnit } = formatWork(bead.difficulty);
  const [isRewardOpen, setIsRewardOpen] = useState(false);

  const handleKeyToggle = (e: React.KeyboardEvent<HTMLDivElement>) => {
    if (e.key === 'Enter' || e.key === ' ') {
      onToggle(bead.id);
    }
  };

  return (
    <div className="border-b border-gray-800/80 ">
      <div
        className={`grid sm:grid-cols-2 md:grid-cols-5 gap-2 p-4 cursor-pointer hover:bg-gray-600 `}
        onClick={() => onToggle(bead.id)}
        onKeyDown={handleKeyToggle}
        role="button"
        tabIndex={0}
      >
        {/* Bead Name */}
        <div className="flex items-center col-span-1 md:col-span-1">
          <div
            className={`mr-2 flex-shrink-0 ${isExpanded ? 'rotate-180' : ''}`}
          >
            <ChevronDown className="h-5 w-5 text-blue-400" />
          </div>
          <span
            className={`text-sm sm:text-base truncate md:truncate-0 ${
              isExpanded ? 'text-white' : 'text-blue-200'
            } font-medium font-mono`}
          >
            {bead.name}
          </span>
          {isExpanded && <div className="ml-2"></div>}
        </div>

        {/* Timestamp */}
        <div className="text-white text-sm sm:text-base">{bead.timestamp}</div>

        {/* Work */}
        <div className="text-white font-medium text-sm sm:text-base">
          {formattedWork} {workUnit}
        </div>

        {/* Transactions */}
        <div className="text-white font-medium text-sm sm:text-base">
          {bead.transactions}
        </div>

        {/* Reward */}
        <div
          className={`text-white font-medium text-sm sm:text-base ${
            isRewardOpen ? 'pb-6' : ''
          }`}
          onClick={(e) => {
            e.stopPropagation();
            setIsRewardOpen(!isRewardOpen);
          }}
        >
          <div className="cursor-pointer">
            <BeadRewardTooltip reward={bead.reward} isOpen={isRewardOpen} />
          </div>
        </div>
      </div>

      {/* Parents */}
      {bead.parents?.length > 0 && (
        <div className="pl-4 sm:pl-10 pr-4 py-2 bg-gray-900/20 border-t border-b border-gray-800/50 overflow-x-auto">
          <div className="flex flex-wrap items-center gap-2 min-w-0">
            <span className="text-blue-300 font-medium text-sm whitespace-nowrap">
              Parents:
            </span>
            <div className="flex flex-wrap gap-2 overflow-x-auto">
              {bead.parents.map((parent) => (
                <button
                  key={parent}
                  className="text-white font-mono text-xs sm:text-sm hover:text-cyan-300 hover:underline truncate max-w-[150px] sm:max-w-[200px]"
                  onClick={(e) => {
                    e.stopPropagation();
                    onParentClick(parent);
                  }}
                >
                  {shortenHash(parent)}
                </button>
              ))}
            </div>
          </div>
        </div>
      )}

      {/* Transaction List */}
      {isExpanded && (
        <div className="overflow-hidden">
          <TransactionList transactions={transactions} />
        </div>
      )}
    </div>
  );
}
