import { motion, AnimatePresence } from 'framer-motion';
import { ChevronDown, Zap } from 'lucide-react';
import TransactionList from './TransactionList';
import { shortenHash } from './lib/utils/shortenHash';
import type { Bead, Transaction } from './lib/types';

interface BeadRowProps {
  bead: Bead;
  isExpanded: boolean;
  onToggle: (beadId: string) => void;
  isActive: boolean;
  transactions: Transaction[];
  onParentClick: (parentHash: string) => void;
}

function formatWork(difficulty: number): { value: string; unit: string } {
  const units = ['GH', 'TH', 'PH', 'EH'];
  let work = difficulty / 1e9;
  let i = 0;

  while (work >= 1000 && i < units.length - 1) {
    work /= 1000;
    i++;
  }

  return {
    value: work >= 1e21 ? work.toExponential(4) : work.toFixed(2),
    unit: units[i],
  };
}

export default function BeadRow({
  bead,
  isExpanded,
  onToggle,
  isActive,
  transactions,
  onParentClick,
}: BeadRowProps) {
  const { value: formattedWork, unit: workUnit } = formatWork(bead.difficulty);

  const handleKeyToggle = (e: React.KeyboardEvent<HTMLDivElement>) => {
    if (e.key === 'Enter' || e.key === ' ') {
      onToggle(bead.id);
    }
  };

  return (
    <div className="border-b border-gray-800/80">
      <motion.div
        className={`grid  sm:grid-cols-2 md:grid-cols-5 gap-2 p-4 cursor-pointer transition-colors duration-300 relative overflow-hidden  ${
          isActive ? 'bg-blue-900/30' : ''
        }`}
        onClick={() => onToggle(bead.id)}
        onKeyDown={handleKeyToggle}
        role="button"
        tabIndex={0}
        whileHover={{
          backgroundColor: 'rgba(30, 58, 138, 0.2)',
          transition: { duration: 0.2 },
        }}
        whileTap={{ scale: 0.98 }}
        layout
      >
        {isActive && (
          <motion.div
            className="absolute inset-0 bg-blue-500/20 rounded-full"
            initial={{ scale: 0, x: '50%', y: '50%' }}
            animate={{ scale: 5, opacity: [1, 0] }}
            transition={{ duration: 0.8 }}
          />
        )}

        <div className="flex items-center relative z-10 col-span-1 md:col-span-1">
          <motion.div
            animate={{ rotate: isExpanded ? 180 : 0 }}
            transition={{ duration: 0.4, type: 'spring', stiffness: 200 }}
            className="mr-2 flex-shrink-0"
          >
            <ChevronDown className="h-5 w-5 text-blue-400" />
          </motion.div>

          <motion.span
            className="text-blue-100 font-medium font-mono text-sm sm:text-base truncate md:truncate-0"
            animate={{
              color: isExpanded ? '#93c5fd' : '#e0e7ff',
            }}
            transition={{ duration: 0.3 }}
          >
            {bead.name}
          </motion.span>

          {isExpanded && (
            <motion.div
              initial={{ opacity: 0, scale: 0 }}
              animate={{ opacity: 1, scale: 1 }}
              className="ml-2"
            >
              <Zap className="h-4 w-4 text-yellow-400" />
            </motion.div>
          )}
        </div>

        <div className="text-gray-300 relative z-10 text-sm sm:text-base">
          {bead.timestamp}
        </div>

        <div className="text-emerald-300 font-medium relative z-10 text-sm sm:text-base">
          {formattedWork} {workUnit}
        </div>

        <div className="text-purple-300 font-medium relative z-10 text-sm sm:text-base">
          <motion.div
            animate={{ scale: isActive ? [1, 1.2, 1] : 1 }}
            transition={{ duration: 0.4 }}
          >
            {bead.transactions}
          </motion.div>
        </div>

        <div className="text-amber-300 font-medium relative z-10 text-sm sm:text-base">
          <motion.div
            animate={{ scale: isActive ? [1, 1.2, 1] : 1 }}
            transition={{ duration: 0.4 }}
          >
            {Number(bead.reward).toFixed(4)} BTC
          </motion.div>
        </div>
      </motion.div>
      {/* Parent row  */}
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
                  className="text-cyan-400 font-mono text-xs sm:text-sm hover:text-cyan-300 hover:underline truncate max-w-[150px] sm:max-w-[200px]"
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

      <AnimatePresence>
        {isExpanded && (
          <motion.div
            initial={{ height: 0, opacity: 0 }}
            animate={{ height: 'auto', opacity: 1 }}
            exit={{ height: 0, opacity: 0 }}
            transition={{
              duration: 0.5,
              type: 'spring',
              stiffness: 100,
              damping: 15,
            }}
            className="overflow-hidden"
          >
            <TransactionList transactions={transactions} />
          </motion.div>
        )}
      </AnimatePresence>
    </div>
  );
}
