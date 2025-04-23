import { motion } from 'framer-motion';
import { BEADS } from '../lib/constants';
import { ChevronDown, Calendar, Search } from 'lucide-react';

interface FilterPanelProps {
  startRef: React.RefObject<HTMLInputElement>;
  endRef: React.RefObject<HTMLInputElement>;
}

export default function FilterPanel({ startRef, endRef }: FilterPanelProps) {
  return (
    <motion.div
      initial={{ height: 0, opacity: 0 }}
      animate={{ height: 'auto', opacity: 1 }}
      exit={{ height: 0, opacity: 0 }}
      transition={{ duration: 0.3 }}
      className="overflow-hidden"
    >
      <div className="grid grid-cols-1 md:grid-cols-4 gap-5 pt-4">
        {/* Miner Select */}
        <div>
          <label className="block mb-2 text-blue-300 font-medium">Miner</label>
          <div className="relative group">
            <select className="w-full bg-gray-900/80 border border-gray-700/80 rounded-lg p-2.5 pr-8 appearance-none focus:border-blue-500 focus:ring-2 focus:ring-blue-500/50 transition-all duration-300 group-hover:border-blue-400/70">
              <option>(All)</option>
              {BEADS.map((bead) => (
                <option key={bead.id} value={bead.id}>
                  {bead.name}
                </option>
              ))}
            </select>
            <div className="absolute inset-y-0 right-0 flex items-center pr-2 pointer-events-none">
              <motion.div
                animate={{ y: [0, 2, 0] }}
                transition={{
                  duration: 1.5,
                  repeat: Number.POSITIVE_INFINITY,
                  repeatType: 'reverse',
                }}
              >
                <ChevronDown className="h-4 w-4 text-blue-400" />
              </motion.div>
            </div>
          </div>
        </div>

        {/* Start Date */}
        <div>
          <label className="block mb-2 text-blue-300 font-medium">
            Start Date
          </label>
          <div className="relative group">
            <input
              ref={startRef}
              type="date"
              defaultValue="2024-07-31"
              className="w-full bg-gray-900/80 border border-gray-700/80 rounded-lg p-2.5 pr-10 text-white focus:border-blue-500 focus:ring-2 focus:ring-blue-500/50 transition-all duration-300 group-hover:border-blue-400/70
                [&::-webkit-calendar-picker-indicator]:opacity-0 [&::-webkit-calendar-picker-indicator]:cursor-pointer"
            />
            <button
              type="button"
              onClick={() => startRef.current?.showPicker()}
              className="absolute right-3 top-1/2 transform -translate-y-1/2"
            >
              <Calendar className="h-5 w-5 text-blue-400 " />
            </button>
          </div>
        </div>

        {/* End Date */}
        <div>
          <label className="block mb-2 text-blue-300 font-medium">
            End Date
          </label>
          <div className="relative group">
            <input
              ref={endRef}
              type="date"
              defaultValue="2024-07-31"
              className="w-full bg-gray-900/80 border border-gray-700/80 rounded-lg p-2.5 pr-10 text-white focus:border-blue-500 focus:ring-2 focus:ring-blue-500/50 transition-all duration-300 group-hover:border-blue-400/70
                [&::-webkit-calendar-picker-indicator]:opacity-0 [&::-webkit-calendar-picker-indicator]:cursor-pointer"
            />
            <button
              type="button"
              onClick={() => endRef.current?.showPicker()}
              className="absolute right-3 top-1/2 transform -translate-y-1/2"
            >
              <Calendar className="h-5 w-5 text-blue-400" />
            </button>
          </div>
        </div>

        {/* Search */}
        <div>
          <label className="block mb-2 text-blue-300 font-medium">Search</label>
          <div className="relative group">
            <input
              type="text"
              className="w-full bg-gray-900/80 border border-gray-700/80 rounded-lg p-2.5 pl-9 focus:border-blue-500 focus:ring-2 focus:ring-blue-500/50 transition-all duration-300 group-hover:border-blue-400/70"
              placeholder="Search transactions, miners..."
            />
            <div className="absolute inset-y-0 left-0 flex items-center pl-2.5">
              <motion.div
                animate={{ scale: [1, 1.1, 1] }}
                transition={{
                  duration: 2,
                  repeat: Number.POSITIVE_INFINITY,
                  repeatType: 'reverse',
                }}
              >
                <Search className="h-4 w-4 text-blue-400" />
              </motion.div>
            </div>
          </div>
        </div>
      </div>
    </motion.div>
  );
}
