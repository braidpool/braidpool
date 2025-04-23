import { motion, AnimatePresence } from "framer-motion"
import { Layers } from "lucide-react"

const borderColorClass = {
  blue: "border-blue-500/30",
  purple: "border-purple-500/30",
  emerald: "border-emerald-500/30",
} 

const bgColorClass = {
  blue: "bg-blue-500/20",
  purple: "bg-purple-500/20",
  emerald: "bg-emerald-500/20",
}

const textColorClass = {
  blue: "text-blue-400",
  purple: "text-purple-400",
  emerald: "text-emerald-400",
}

export function BlockGrid({
    blockVisualizationData,
    selectedBlock,
    setSelectedBlock,
    animateBlocks,
    isLoaded,
  }: {
    blockVisualizationData: any[]
    selectedBlock: string | null
    setSelectedBlock: (id: string | null) => void
    animateBlocks: boolean
    isLoaded: boolean
  }) {

    if (!isLoaded) {
      return (
        <div className="absolute inset-0 flex items-center justify-center">
          <div className="w-12 h-12 border-4 border-blue-500 border-t-transparent rounded-full animate-spin"></div>
        </div>
      )
    }

    return (
      <div className="grid grid-cols-1 sm:grid-cols-2 md:grid-cols-3 lg:grid-cols-4 gap-6">
        {blockVisualizationData.map((block, index) => {
          const blockColor = block.color || "blue" // Fallback to "blue" if color is undefined
          
          return (
            <motion.div
              key={block.id}
              className={`relative border ${borderColorClass[blockColor]} rounded-lg p-4 bg-gray-900/50 backdrop-blur-sm overflow-hidden`}
              initial={{ opacity: 0, y: 20, scale: 0.95 }}
              animate={{
                opacity: animateBlocks ? 1 : 0,
                y: animateBlocks ? 0 : 20,
                scale: animateBlocks ? 1 : 0.95,
              }}
              transition={{ duration: 0.5, delay: index * 0.05 }}
              whileHover={{
                scale: 1.03,
                boxShadow: `0 0 20px rgba(59, 130, 246, 0.3)`,
              }}
              onClick={() => setSelectedBlock(selectedBlock === block.id ? null : block.id)}
              style={{ willChange: "transform, opacity" }} // Performance optimization
            >
              <div className="flex justify-between items-start mb-3">
                <div className={`${bgColorClass[blockColor]} p-2 rounded-lg`}>
                  <Layers className={`h-5 w-5 ${textColorClass[blockColor]}`} />
                </div>
                <div className="bg-gray-800/70 px-2 py-1 rounded text-xs font-mono text-gray-300">
                  #{block.height}
                </div>
              </div>
              <h3 className="text-lg font-semibold text-white mb-2 truncate">Block {block.height}</h3>
              <div className="space-y-1 text-sm">
                <div className="flex justify-between">
                  <span className="text-gray-400">Transactions:</span>
                  <span className="text-purple-300 font-medium">{block.transactions}</span>
                </div>
                <div className="flex justify-between">
                  <span className="text-gray-400">Size:</span>
                  <span className="text-blue-300 font-medium">{block.size} KB</span>
                </div>
                <div className="flex justify-between">
                  <span className="text-gray-400">Miner:</span>
                  <span className="text-emerald-300 font-medium">{block.miner}</span>
                </div>
                <div className="flex justify-between">
                  <span className="text-gray-400">Difficulty:</span>
                  <span className="text-amber-300 font-medium">{block.difficulty}</span>
                </div>
              </div>
              <AnimatePresence>
                {selectedBlock === block.id && (
                  <motion.div
                    initial={{ height: 0, opacity: 0 }}
                    animate={{ height: "auto", opacity: 1 }}
                    exit={{ height: 0, opacity: 0 }}
                    transition={{ duration: 0.3 }}
                    className="mt-3 pt-3 border-t border-gray-700/50"
                  >
                    <div className="space-y-1 text-sm">
                      <div className="flex justify-between">
                        <span className="text-gray-400">Timestamp:</span>
                        <span className="text-gray-300">{new Date(block.timestamp).toLocaleString()}</span>
                      </div>
                      <div className="flex justify-between">
                        <span className="text-gray-400">Confirmations:</span>
                        <span className="text-green-300">{block.confirmations}</span>
                      </div>
                      <div className="flex justify-between">
                        <span className="text-gray-400">Nonce:</span>
                        <span className="text-gray-300 font-mono">{Math.floor(Math.random() * 1000000000)}</span>
                      </div>
                    </div>
                    <button 
                      className="w-full mt-3 py-1.5 bg-blue-600/20 hover:bg-blue-600/30 rounded-md text-blue-300 text-sm transition-colors"
                      aria-label={`View details of block ${block.height}`}
                    >
                      View Details
                    </button>
                  </motion.div>
                )}
              </AnimatePresence>
              {block.confirmations < 3 && (
                <motion.div
                  className="absolute top-2 right-2 h-2 w-2 rounded-full bg-green-500"
                  animate={{ scale: [1, 1.5, 1] }}
                  transition={{ duration: 2, repeat: Number.POSITIVE_INFINITY }}
                />
              )}
            </motion.div>
          )
        })}
      </div>
    )
  }
