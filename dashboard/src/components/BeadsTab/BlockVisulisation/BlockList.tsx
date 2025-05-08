import { motion } from 'framer-motion';

export function BlockList({
  blockVisualizationData,
  animateBlocks,
  isLoaded,
}: {
  blockVisualizationData: any[];
  animateBlocks: boolean;
  isLoaded: boolean;
}) {
  if (!isLoaded)
    return (
      <div className="flex justify-center py-12">
        <div className="w-12 h-12 border-4 border-blue-500 border-t-transparent rounded-full animate-spin"></div>
      </div>
    );
  return (
    <div className="space-y-4">
      <div className="grid grid-cols-7 gap-4 px-4 py-2 border-b border-gray-800/80 text-sm font-medium text-gray-400 sm:grid sm:grid-cols-3 sm-grid-rows-2">
        <div>Height</div>
        <div>Time</div>
        <div>Miner</div>
        <div>Transactions</div>
        <div>Size</div>
        <div>Difficulty</div>
        <div></div>
      </div>
      {blockVisualizationData.map((block, index) => (
        <motion.div
          key={block.id}
          className="grid grid-cols-7 gap-4 px-4 py-3 rounded-lg items-center sm:grid sm:grid-rows-3 hover:bg-gray-800/30 transition-colors h-15"
          initial={{ opacity: 0, y: 20 }}
          animate={{
            opacity: animateBlocks ? 1 : 0,
            y: animateBlocks ? 0 : 20,
          }}
          transition={{ duration: 0.3, delay: index * 0.03 }}
        >
          <div className="font-medium text-white">#{block.height}</div>
          <div className="text-gray-400 text-sm">
            {new Date(block.timestamp).toLocaleTimeString()}
          </div>
          <div className="text-emerald-300">{block.miner}</div>
          <div className="text-purple-300">{block.transactions}</div>
          <div className="text-blue-300">{block.size} KB</div>
          <div className="text-amber-300">{block.difficulty}</div>
          <div>
            <button className="px-3 py-1 bg-blue-600/20 hover:bg-blue-600/30 rounded text-blue-300 text-sm transition-colors">
              Details
            </button>
          </div>
          {index < 3 && (
            <motion.div
              className="absolute left-0 top-0 bottom-0 w-1 bg-green-500 rounded-l-lg"
              animate={{ opacity: [0.5, 1, 0.5] }}
              transition={{ duration: 2, repeat: Number.POSITIVE_INFINITY }}
            />
          )}
        </motion.div>
      ))}
    </div>
  );
}
