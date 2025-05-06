import { motion } from 'framer-motion';
import { BarChart3, Layers, Cpu, Database } from 'lucide-react';

interface DashboardHeaderProps {
  headerOpacity: any;
  headerScale: any;
  activeTab: string;
  setActiveTab: (tab: string) => void;
}

const TABS = [
  { key: 'miners', label: 'Miners' },
  { key: 'trends', label: 'Trends' },
  { key: 'blocks', label: 'Blocks' },
];
export default function DashboardHeader({
  headerOpacity,
  headerScale,
  activeTab,
  setActiveTab,
}: {
  headerOpacity: any;
  headerScale: any;
  activeTab: string;
  setActiveTab: (tab: string) => void;
}) {
  return (
    <motion.div
      style={{ opacity: headerOpacity, scale: headerScale }}
      className="sticky top-0 z-50 pt-4 pb-6 backdrop-blur-md bg-black/30"
    >
      <div className="flex flex-col md:flex-row justify-between items-start md:items-center gap-4 mb-6">
        <motion.div
          initial={{ opacity: 0, y: -30 }}
          animate={{ opacity: 1, y: 0 }}
          transition={{ duration: 0.8, type: 'spring' }}
          className="w-full md:w-auto"
        >
          <h1 className="text-3xl sm:text-4xl md:text-5xl font-bold bg-clip-text text-transparent bg-gradient-to-r from-blue-400 via-purple-500 to-blue-500 drop-shadow-[0_0_15px_rgba(59,130,246,0.5)] tracking-tight">
            Beads Explorer
          </h1>

          {/* Animated underline */}
          <motion.div
            className="h-1 bg-gradient-to-r from-blue-500 to-purple-500 rounded-full"
            initial={{ width: 0, opacity: 0 }}
            animate={{ width: '30%', opacity: 1 }}
            transition={{ delay: 0.5, duration: 0.8 }}
          />
        </motion.div>

        {/* Action buttons */}
        <motion.div
          initial={{ opacity: 0, y: -20 }}
          animate={{ opacity: 1, y: 0 }}
          transition={{ duration: 0.6, delay: 0.3 }}
          className="flex gap-3 w-full md:w-auto justify-end "
        >
          <motion.button
            className="relative px-3 sm:px-4 py-2 rounded-lg text-white text-sm sm:text-base font-medium overflow-hidden  bg-[#1D2B53] hover:bg-black "
            whileHover={{ scale: 1.05 }}
            whileTap={{ scale: 0.97 }}
          >
            <span className="relative z-10 flex items-center justify-center gap-2">
              <BarChart3 className="w-4 h-4" />
              <span className="">Analytics</span>
            </span>
          </motion.button>
          <motion.button
            className="relative px-3 sm:px-4 py-2 rounded-lg text-white text-sm sm:text-base font-medium overflow-hidden   bg-[#1D2B53] hover:bg-black"
            whileTap={{ scale: 0.97 }}
          >
            <span className="relative z-10 flex items-center justify-center gap-2">
              <Database className="w-4 h-4" />
              <span className="">Export Data</span>
            </span>
          </motion.button>
        </motion.div>
      </div>

      {/* Tab navigation */}
      <motion.div
        initial={{ opacity: 0, y: 20 }}
        animate={{ opacity: 1, y: 0 }}
        transition={{ duration: 0.6, delay: 0.4 }}
        className="flex border-b border-gray-800/70 mb-6 overflow-x-auto pb-1 scrollbar-hide"
      >
        {[
          {
            id: 'beads',
            label: 'Beads',
            icon: <Cpu className="w-4 h-4" />,
          },
          {
            id: 'trends',
            label: 'Trends',
            icon: <BarChart3 className="w-4 h-4" />,
          },
          {
            id: 'blocks',
            label: 'Blocks',
            icon: <Layers className="w-4 h-4" />,
          },
        ].map((tab) => (
          <motion.button
            key={tab.id}
            className={`flex items-center gap-1 sm:gap-2 px-3 sm:px-4 py-3 font-medium relative whitespace-nowrap text-sm sm:text-base ${
              activeTab === tab.id
                ? 'text-blue-400'
                : 'text-gray-400 hover:text-gray-200'
            }`}
            onClick={() => setActiveTab(tab.id)}
            whileHover={{ y: -2 }}
            whileTap={{ scale: 0.97 }}
          >
            {tab.icon}
            {tab.label}
            {activeTab === tab.id && (
              <motion.div
                className="absolute bottom-0 left-0 right-0 h-0.5 bg-blue-500"
                layoutId="activeTab"
                initial={{ opacity: 0 }}
                animate={{ opacity: 1 }}
                transition={{ type: 'spring', stiffness: 300, damping: 30 }}
              />
            )}
          </motion.button>
        ))}
      </motion.div>
    </motion.div>
  );
}
