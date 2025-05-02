import { motion, AnimatePresence } from 'framer-motion';
import { ChevronDown, Zap } from 'lucide-react';
import TransactionList from './TransactionList';
import { shortenHash } from './lib/utils/shortenHash';
import type { Bead, Transaction } from './lib/types';
interface MinerRowProps {
  bead: Bead;
  isExpanded: boolean;
  onToggle: (beadId: string) => void;
  isActive: boolean;
  transactions: Transaction[];
  onParentClick: (parentHash: string) => void;
}
export default function BeadRow({
  bead,
  isExpanded,
  onToggle,
  isActive,
  transactions,
  onParentClick,
}: MinerRowProps) {
  let work = bead.difficulty;
let workUnit = 'GH';

if (work >= 1e18) {
  work = work / 1e18;
  workUnit = 'EH';
} else if (work >= 1e15) {
  work = work / 1e15;
  workUnit = 'PH';
} else if (work >= 1e12) {
  work = work / 1e12;
  workUnit = 'TH';
} else if (work >= 1e9) {
  work = work / 1e9;
  workUnit = 'GH';
}

const formattedWork =
  work >= 1e21 ? work.toExponential(4) : work.toFixed(2);



  return (
    <div className="border-b border-gray-800/80 ">
      <motion.div
        className={`grid grid-cols-5 p-4 cursor-pointer transition-colors duration-300 relative overflow-hidden ${
          isActive ? 'bg-blue-900/30' : ''
        }`}
        onClick={() => onToggle(bead.id)}
        whileHover={{
          backgroundColor: 'rgba(30, 58, 138, 0.2)',
          transition: { duration: 0.2 },
        }}
        whileTap={{ scale: 0.98 }}
      >
        {/* Ripple effect on click */}
        {isActive && (
          <motion.div
            className="absolute inset-0 bg-blue-500/20 rounded-full"
            initial={{ scale: 0, x: '50%', y: '50%' }}
            animate={{ scale: 5, opacity: [1, 0] }}
            transition={{ duration: 0.8 }}
          />
        )}

        <div className="flex items-center relative z-10">
          <motion.div
            animate={{ rotate: isExpanded ? 180 : 0 }}
            transition={{ duration: 0.4, type: 'spring', stiffness: 200 }}
            className="mr-2"
          >
            <ChevronDown className="h-5 w-5 text-blue-400" />
          </motion.div>
          <motion.span
            className="text-blue-100 font-medium font-mono"
            animate={{
              color: isExpanded ? '#93c5fd' : '#e0e7ff',
            }}
            transition={{ duration: 0.3 }}
          >
            {bead.name}
          </motion.span>

          {/* Animated indicator */}
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
        <div className="text-gray-300 relative z-10">{bead.timestamp}</div>
        <div className="text-emerald-300 font-medium relative z-10 mt-2 md:mt-0 md:col-span-1">
          {formattedWork} {workUnit}
        </div>
        <div className="text-purple-300 font-medium   relative z-10 ml-8">
          <motion.div
            animate={{ scale: isActive ? [1, 1.2, 1] : 1 }}
            transition={{ duration: 0.4 }}
          >
            {bead.transactions}
          </motion.div>
        </div>
        <div className="text-amber-300 font-medium relative z-10 mt-2 md:mt-0 md:col-span-1">
          <motion.div
            animate={{ scale: isActive ? [1, 1.2, 1] : 1 }}
            transition={{ duration: 0.4 }}
          >
            {Number(bead.reward).toFixed(4)} BTC
          </motion.div>
        </div>
      </motion.div>

      {/* Parents row */}
      <div className="pl-10 pr-4 py-2 bg-gray-900/20 border-t border-b border-gray-800/50">
        <div className="flex items-center gap-2">
          <span className="text-blue-300 font-medium">Parents:</span>
          <div className="flex flex-wrap gap-2">
            {bead.parents.map((parent) => (
              <button
                key={parent}
                className="text-cyan-400 font-mono text-sm hover:text-cyan-300 hover:underline"
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
