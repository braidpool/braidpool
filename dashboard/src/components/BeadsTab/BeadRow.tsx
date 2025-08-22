import React from 'react';
import TransactionList from './TransactionList';
import { shortenHash, formatWork, useCopyToClipboard } from './lib/Utils';
import type { BeadRowProps } from './lib/Types';
import { ChevronDown } from 'lucide-react';

export default function BeadRow({
  bead,
  isExpanded,
  onToggle,
  transactions,
}: BeadRowProps) {
  const { value: formattedWork, unit: workUnit } = formatWork(bead.difficulty);
  const handleKeyToggle = (e: React.KeyboardEvent<HTMLDivElement>) => {
    if (e.key === 'Enter' || e.key === ' ') {
      onToggle(bead.id);
    }
  };

  const { copied, copy } = useCopyToClipboard();
  return (
    <div className="border-b border-gray-800/80">
      <div
        className="grid max-sm:grid-cols-3 md:grid-cols-5 gap-2 p-4 cursor-pointer hover:bg-gray-600"
        onClick={() => onToggle(bead.id)}
        onKeyDown={handleKeyToggle}
        role="button"
        tabIndex={0}
      >
        {/* Bead Name */}
        <div className="flex items-center col-span-1">
          <div
            className={`mr-2 flex-shrink-0 ${isExpanded ? 'rotate-180' : ''}`}
          >
            <ChevronDown className="h-5 w-5 text-blue-400" />
          </div>
          <span
            className={`text-sm sm:text-base truncate ${isExpanded ? 'text-white' : 'text-blue-200'}
        font-medium font-mono`}
          >
            {bead.name.replace(/^#/, '')}
          </span>
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
        <div className="text-white font-medium text-sm sm:text-base">
          {`${bead.reward.toFixed(2)} BTC`}
        </div>
      </div>

      {/* Parents */}
      {bead.parents?.length > 0 && (
        <div className="pl-4 sm:pl-10 pr-4 py-2 bg-gray-900/20 border-t border-b border-gray-800/50 overflow-x-auto">
          <div className="flex flex-wrap items-center gap-2 min-w-0">
            <span className="text-blue-300 font-medium text-sm whitespace-nowrap">
              Parents:
            </span>
            <div className="flex flex-wrap gap-4 overflow-x-auto">
              {bead.parents.map((parent) => (
                <div key={parent} className="relative">
                  <button
                    className="text-white font-mono text-xs sm:text-sm hover:text-cyan-300 hover:underline truncate max-w-[150px] sm:max-w-[200px]"
                    onClick={(e) => {
                      e.stopPropagation();
                      copy(parent);
                    }}
                  >
                    {shortenHash(parent)}
                  </button>
                  {copied === parent && (
                    <span className=" px-2 text-green-400 text-xs">
                      Copied!
                    </span>
                  )}
                </div>
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
