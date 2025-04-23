import type React from 'react';

import { useState } from 'react';
import { motion, AnimatePresence } from 'framer-motion';
import { ChevronDown, Calendar } from 'lucide-react';

import { TIME_RANGES } from './lib/constants';

export default function DateRangePicker({
  timeRange,
  setTimeRange,
}: {
  timeRange: string;
  setTimeRange: (range: string) => void;
}) {
  const [isOpen, setIsOpen] = useState(false);

  const handleSelect = (range: string) => {
    setTimeRange(range);
    setIsOpen(false);
  };

  return (
    <div className="relative">
      <button
        className="flex items-center gap-2 bg-gray-900/50 rounded-lg px-4 py-2 text-sm font-medium text-gray-200 hover:bg-gray-800/50 transition-colors"
        onClick={() => setIsOpen(!isOpen)}
      >
        <Calendar className="h-4 w-4 text-blue-400" />
        <span>
          {TIME_RANGES.find((r) => r.value === timeRange)?.label ||
            'Custom Range'}
        </span>
        <motion.div
          animate={{ rotate: isOpen ? 180 : 0 }}
          transition={{ duration: 0.2 }}
        >
          <ChevronDown className="h-4 w-4 text-gray-400" />
        </motion.div>
      </button>

      <AnimatePresence>
        {isOpen && (
          <motion.div
            className="absolute top-full left-0 mt-2 w-48 bg-gray-900/90 backdrop-blur-md border border-gray-800 rounded-lg shadow-lg z-50"
            initial={{ opacity: 0, y: -10 }}
            animate={{ opacity: 1, y: 0 }}
            exit={{ opacity: 0, y: -10 }}
            transition={{ duration: 0.2 }}
          >
            <div className="p-2">
              {TIME_RANGES.map((range) => (
                <button
                  key={range.value}
                  className={`w-full text-left px-3 py-2 rounded-md text-sm ${
                    timeRange === range.value
                      ? 'bg-blue-600/30 text-blue-200'
                      : 'text-gray-300 hover:bg-gray-800/50'
                  }`}
                  onClick={() => handleSelect(range.value)}
                >
                  {range.label}
                </button>
              ))}
              <div className="border-t border-gray-800 my-1 pt-1">
                <button
                  className="w-full text-left px-3 py-2 rounded-md text-sm text-gray-300 hover:bg-gray-800/50"
                  onClick={() => {
                    // Custom date range functionality would go here
                    setIsOpen(false);
                  }}
                >
                  Custom Range...
                </button>
              </div>
            </div>
          </motion.div>
        )}
      </AnimatePresence>
    </div>
  );
}
