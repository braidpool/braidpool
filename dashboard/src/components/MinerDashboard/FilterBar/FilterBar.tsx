import React, { useState, useRef } from 'react';
import { motion, AnimatePresence } from 'framer-motion';
import { ChevronDown, Filter } from 'lucide-react';
import DateRangePicker from '../DateRangePicker';
import FilterPanel from './FilterPanel';

export interface FilterBarProps {
  timeRange: string;
  setTimeRange: (range: string) => void;
}

export function FilterBar({ timeRange, setTimeRange }: FilterBarProps) {
  const [showFilters, setShowFilters] = useState(false);
  const startRef = useRef<HTMLInputElement>(null);
  const endRef = useRef<HTMLInputElement>(null);

  return (
    <motion.div
      className="relative border border-gray-800/50 rounded-xl p-5 mb-8 bg-black/30 backdrop-blur-md shadow-[0_0_25px_rgba(59,130,246,0.15)] overflow-hidden"
      initial={{ opacity: 0, y: 50, scale: 0.9 }}
      animate={{ opacity: 1, y: 0, scale: 1 }}
      transition={{ duration: 0.6, delay: 0.2, type: 'spring' }}
    >
      {/* Subtle border accent */}
      <div className="absolute top-0 left-0 w-1 h-full bg-[#3986e8]" />

      <div className="flex flex-col space-y-4">
        <div className="flex justify-between items-center">
          <div className="flex items-center gap-2">
            <Filter className="h-5 w-5 text-blue-400" />
            <h3 className="text-lg font-medium text-white">Filters</h3>
          </div>
          <div className="flex items-center gap-3">
            <DateRangePicker
              timeRange={timeRange}
              setTimeRange={setTimeRange}
            />
            <motion.button
              className="bg-gray-900/50 rounded-lg p-2 text-gray-300 hover:text-white hover:bg-gray-800/70 transition-colors"
              whileHover={{ scale: 1.05 }}
              whileTap={{ scale: 0.95 }}
              onClick={() => setShowFilters(!showFilters)}
            >
              <motion.div
                className="flex items-center justify-center"
                animate={{ rotate: showFilters ? 180 : 0 }}
                transition={{ duration: 0.2 }}
              >
                <ChevronDown className="h-5 w-5" />
              </motion.div>
            </motion.button>
          </div>
        </div>

        <AnimatePresence>
          {showFilters && <FilterPanel startRef={startRef} endRef={endRef} />}
        </AnimatePresence>
      </div>
    </motion.div>
  );
}
