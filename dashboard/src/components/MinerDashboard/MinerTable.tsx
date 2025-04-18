import { useState } from "react";
import { motion, AnimatePresence } from "framer-motion";
import { ChevronDown, Activity, Zap } from "lucide-react";

interface MinerTableProps {
  isLoaded: boolean;
}

interface MinerData {
  id: string;
  timestamp: string;
  transactionCount: number;
  transactions: {
    hash: string;
    timestamp: string;
    count: number;
  }[];
}

export default function MinerTable({ isLoaded }: MinerTableProps) {
  const [expandedMiners, setExpandedMiners] = useState<Record<string, boolean>>(
    {
      miner1: true,
      miner2: false,
    },
  );
  const [activeMiner, setActiveMiner] = useState<string | null>(null);

  // Mock data - in a real app, this would come from props or API
  const minersData: Record<string, MinerData> = {
    miner1: {
      id: "miner1",
      timestamp: "2025-04-15 14:23",
      transactionCount: 5,
      transactions: [
        {
          hash: "f68b21db...de3b0803",
          timestamp: "2025-04-15 14:23",
          count: 12,
        },
        {
          hash: "964aebde...4813c0a6",
          timestamp: "2025-04-15 14:33",
          count: 7,
        },
        {
          hash: "2c1a7f84...477aec04",
          timestamp: "2025-04-30 09:17",
          count: 12,
        },
      ],
    },
    miner2: {
      id: "miner2",
      timestamp: "2025-04-30 09:17",
      transactionCount: 9,
      transactions: [
        {
          hash: "a1b2c3d4...e5f6g7h8",
          timestamp: "2025-04-30 09:17",
          count: 8,
        },
        {
          hash: "i9j0k1l2...m3n4o5p6",
          timestamp: "2025-04-30 10:45",
          count: 5,
        },
      ],
    },
  };

  const toggleMiner = (minerId: string) => {
    setExpandedMiners((prev) => ({
      ...prev,
      [minerId]: !prev[minerId],
    }));
    setActiveMiner(minerId);

    setTimeout(() => {
      setActiveMiner(null);
    }, 1000);
  };

  return (
    <motion.div
      initial={{ opacity: 0, y: 50, rotateX: 5 }}
      animate={{ opacity: isLoaded ? 1 : 0, y: isLoaded ? 0 : 50, rotateX: 0 }}
      transition={{ duration: 0.7, delay: 0.4, type: "spring" }}
      className="border border-gray-800/50 rounded-xl mb-8 bg-black/30 backdrop-blur-md shadow-[0_0_25px_rgba(59,130,246,0.15)] overflow-hidden transform-gpu"
    >
      {/* Table header */}
      <div className="grid grid-cols-3 p-4 border-b border-gray-800/80 font-medium relative overflow-hidden">
        <motion.div
          className="absolute inset-0 bg-gradient-to-r from-blue-900/30 via-purple-900/30 to-blue-900/30"
          animate={{
            backgroundPosition: ["0% 0%", "100% 0%", "0% 0%"],
          }}
          transition={{
            duration: 8,
            repeat: Number.POSITIVE_INFINITY,
            repeatType: "loop",
          }}
        />
        <div className="text-blue-200 font-semibold relative z-10">Miner</div>
        <div className="text-blue-200 font-semibold relative z-10">
          Timestamp
        </div>
        <div className="text-blue-200 font-semibold relative z-10">
          Transactions
        </div>
      </div>

      {/* Loading state */}
      {!isLoaded && (
        <div className="p-8">
          <div className="h-12 bg-gray-800/50 rounded-md animate-pulse mb-4"></div>
          <div className="h-12 bg-gray-800/50 rounded-md animate-pulse"></div>
        </div>
      )}

      {/* Miner data */}
      {isLoaded && (
        <>
          {Object.entries(minersData).map(([minerId, miner]) => (
            <div
              key={minerId}
              className={
                minerId === "miner1" ? "border-b border-gray-800/80" : ""
              }
            >
              <MinerRow
                miner={minerId}
                expanded={!!expandedMiners[minerId]}
                active={activeMiner === minerId}
                timestamp={miner.timestamp}
                transactionCount={miner.transactions.reduce(
                  (acc, curr) => acc + curr.count,
                  0,
                )}
                onToggle={toggleMiner}
              />

              <AnimatePresence>
                {expandedMiners[minerId] && (
                  <ExpandedMinerContent transactions={miner.transactions} />
                )}
              </AnimatePresence>
            </div>
          ))}
        </>
      )}
    </motion.div>
  );
}

interface MinerRowProps {
  miner: string;
  expanded: boolean;
  active: boolean;
  timestamp: string;
  transactionCount: number;
  onToggle: (miner: string) => void;
}

function MinerRow({
  miner,
  expanded,
  active,
  timestamp,
  transactionCount,
  onToggle,
}: MinerRowProps) {
  return (
    <motion.div
      className={`grid grid-cols-3 p-4 cursor-pointer transition-colors duration-300 relative overflow-hidden ${
        active ? "bg-blue-900/30" : ""
      }`}
      onClick={() => onToggle(miner)}
      whileHover={{
        backgroundColor: "rgba(30, 58, 138, 0.2)",
        transition: { duration: 0.2 },
      }}
      whileTap={{ scale: 0.98 }}
    >
      {active && (
        <motion.div
          className="absolute inset-0 bg-blue-500/20 rounded-full"
          initial={{ scale: 0, x: "50%", y: "50%" }}
          animate={{ scale: 5, opacity: [1, 0] }}
          transition={{ duration: 0.8 }}
        />
      )}

      <div className="flex items-center relative z-10">
        <motion.div
          animate={{ rotate: expanded ? 180 : 0 }}
          transition={{ duration: 0.4, type: "spring", stiffness: 200 }}
          className="mr-2"
        >
          <ChevronDown className="h-5 w-5 text-blue-400" />
        </motion.div>
        <motion.span
          className="text-blue-100 font-medium"
          animate={{
            color: expanded ? "#93c5fd" : "#e0e7ff",
          }}
          transition={{ duration: 0.3 }}
        >
          {miner}
        </motion.span>

        {expanded && (
          <motion.div
            initial={{ opacity: 0, scale: 0 }}
            animate={{ opacity: 1, scale: 1 }}
            className="ml-2"
          >
            <Zap className="h-4 w-4 text-yellow-400" />
          </motion.div>
        )}
      </div>
      <div className="text-gray-300 relative z-10">{timestamp}</div>
      <div className="text-purple-300 font-medium relative z-10">
        <motion.div
          animate={{ scale: active ? [1, 1.2, 1] : 1 }}
          transition={{ duration: 0.4 }}
        >
          {transactionCount}
        </motion.div>
      </div>
    </motion.div>
  );
}

interface ExpandedMinerContentProps {
  transactions: {
    hash: string;
    timestamp: string;
    count: number;
  }[];
}

function ExpandedMinerContent({ transactions }: ExpandedMinerContentProps) {
  return (
    <motion.div
      initial={{ height: 0, opacity: 0 }}
      animate={{ height: "auto", opacity: 1 }}
      exit={{ height: 0, opacity: 0 }}
      transition={{
        duration: 0.5,
        type: "spring",
        stiffness: 100,
        damping: 15,
      }}
      className="overflow-hidden"
    >
      <div className="pl-10 pr-4 pb-3 bg-gradient-to-b from-blue-900/20 to-transparent">
        <motion.div
          className="text-blue-400 mb-3 font-medium flex items-center"
          initial={{ x: -20, opacity: 0 }}
          animate={{ x: 0, opacity: 1 }}
          transition={{ delay: 0.1 }}
        >
          <Activity className="h-4 w-4 mr-2" />
          Included {transactions.length} Transactions
        </motion.div>

        <motion.div
          variants={{
            hidden: { opacity: 0 },
            show: {
              opacity: 1,
              transition: {
                staggerChildren: 0.1,
              },
            },
          }}
          initial="hidden"
          animate="show"
        >
          {transactions.map((transaction, index) => (
            <TransactionRow
              key={transaction.hash}
              hash={transaction.hash}
              timestamp={transaction.timestamp}
              count={transaction.count}
              delay={index * 0.2}
            />
          ))}
        </motion.div>
      </div>
    </motion.div>
  );
}

interface TransactionRowProps {
  hash: string;
  timestamp: string;
  count: number;
  delay: number;
}

function TransactionRow({
  hash,
  timestamp,
  count,
  delay,
}: TransactionRowProps) {
  return (
    <motion.div
      variants={{
        hidden: { y: 20, opacity: 0 },
        show: { y: 0, opacity: 1 },
      }}
      className="grid grid-cols-3 py-2.5 rounded-lg transition-all duration-300 group relative"
      whileHover={{ scale: 1.01, backgroundColor: "rgba(30, 58, 138, 0.2)" }}
    >
      <div className="absolute inset-0 bg-blue-500/5 opacity-0 group-hover:opacity-100 rounded-lg transition-opacity duration-300"></div>

      <div className="text-cyan-400 font-mono relative z-10 group-hover:text-cyan-300 transition-colors duration-300">
        <motion.span
          animate={{ opacity: [0.7, 1, 0.7] }}
          transition={{ duration: 3, repeat: Number.POSITIVE_INFINITY, delay }}
        >
          {hash}
        </motion.span>
      </div>
      <div className="text-gray-400 relative z-10 group-hover:text-gray-300 transition-colors duration-300">
        {timestamp}
      </div>
      <div className="text-purple-300 font-medium relative z-10 group-hover:text-purple-200 transition-colors duration-300">
        <motion.span
          whileHover={{ scale: 1.2 }}
          transition={{ type: "spring", stiffness: 400 }}
        >
          {count}
        </motion.span>
      </div>
    </motion.div>
  );
}
