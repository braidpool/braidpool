import React, { useState } from 'react';
import TransactionList from './TransactionList';
import { shortenHash, formatWork } from './lib/Utils';
import type { BeadRowProps } from './lib/Types';
import { shortenHash, formatWork } from './lib/Utils';
import type { BeadRowProps } from './lib/Types';
import { BeadRewardTooltip } from './BeadRewardTooltip';
import useCopyToClipboard from './lib/Utils';
import useCopyToClipboard from './lib/Utils';
export default function BeadRow({
  bead,
  transactions,
}: BeadRowProps) {
  const { value: formattedWork, unit: workUnit } = formatWork(bead.difficulty);
  const [isRewardOpen, setIsRewardOpen] = useState(false);
  const handleKeyToggle = (e: React.KeyboardEvent<HTMLDivElement>) => {
  
  };

  const { copied, copy } = useCopyToClipboard();
  const { copied, copy } = useCopyToClipboard();
  return (
    <div className="border-b border-gray-800/80">
      <div
        className="grid max-sm:grid-cols-3 md:grid-cols-5 gap-2 t p-4 cursor-pointer hover:bg-gray-600"
        
        onKeyDown={handleKeyToggle}
        role="button"
        tabIndex={0}
      >
      >
        {/* Bead Name */}
        <div className="flex items-center col-span-1 md:col-span-1">         
          <span
            className={`text-sm sm:text-base truncate 
             font-medium font-mono`}
          >
            {bead.name}
          </span>
          </span>
        </div>

        {/* Timestamp */}
        <div className="text-white text-sm sm:text-base">{bead.timestamp}</div>
        <div className="text-white text-sm sm:text-base">{bead.timestamp}</div>

        {/* Work */}
        <div className="text-white font-medium text-sm sm:text-base">
        <div className="text-white font-medium text-sm sm:text-base">
          {formattedWork} {workUnit}
        </div>

        {/* Transactions */}
        <div className="text-white font-medium text-sm sm:text-base">
          {bead.transactions}
        <div className="text-white font-medium text-sm sm:text-base">
          {bead.transactions}
        </div>

        {/* Reward */}
        {/* Reward */}
        <div
          className={`text-white font-medium text-sm sm:text-base ${
          className={`text-white font-medium text-sm sm:text-base ${
            isRewardOpen ? 'pb-6' : ''
          }`}
          onClick={(e) => {
            e.stopPropagation();
            setIsRewardOpen(!isRewardOpen);
          }}
        >
          <div className="cursor-pointer">
          <div className="cursor-pointer">
            <BeadRewardTooltip reward={bead.reward} isOpen={isRewardOpen} />
          </div>
          </div>
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
            <div className="flex flex-wrap gap-4 overflow-x-auto">
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
       
        <div className="overflow-hidden">
          <TransactionList transactions={transactions} />
        </div>
      
    </div>
  );
}
