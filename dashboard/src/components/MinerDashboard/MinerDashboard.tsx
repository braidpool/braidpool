import { useState, useEffect } from "react";
import Particles from "./Particles";
import Filters from "./Filters";
import MinerTable from "./MinerTable";
import MiningChart from "./MinerChart";
import { motion } from "framer-motion";

export default function MinedSharesExplorer() {
  const [isLoaded, setIsLoaded] = useState(false);
  const [showParticles, setShowParticles] = useState(false);

  useEffect(() => {
    const timer = setTimeout(() => {
      setIsLoaded(true);
    }, 800);

    const particleTimer = setTimeout(() => {
      setShowParticles(true);
    }, 1500);

    return () => {
      clearTimeout(timer);
      clearTimeout(particleTimer);
    };
  }, []);

  return (
    <div className="min-h-screen bg-gradient-to-br from-gray-900 via-[#0a0b1e] to-black text-white p-6 overflow-hidden relative perspective-1000">
      {/* Animated background particles */}
      {showParticles && <Particles />}

      {/* Animated gradient background */}
      <div className="absolute inset-0 -z-10 bg-[radial-gradient(ellipse_at_top,_var(--tw-gradient-stops))] from-blue-900/20 via-gray-900/10 to-transparent animate-pulse-slow"></div>

      {/* Header with 3D effect */}
      <motion.div
        initial={{ opacity: 0, y: -50, rotateX: -20 }}
        animate={{ opacity: 1, y: 0, rotateX: 0 }}
        transition={{ duration: 0.8, type: "spring", bounce: 0.4 }}
        className="relative"
      >
        <h1 className="text-5xl font-bold mb-8 bg-clip-text text-transparent bg-gradient-to-r from-blue-400 via-purple-500 to-blue-500 drop-shadow-[0_0_15px_rgba(59,130,246,0.5)] tracking-tight">
          Mined Shares Explorer
        </h1>
        <motion.div
          className="h-1 bg-gradient-to-r from-blue-500 to-purple-500 rounded-full"
          initial={{ width: 0, opacity: 0 }}
          animate={{ width: "40%", opacity: 1 }}
          transition={{ delay: 0.5, duration: 0.8 }}
        />
      </motion.div>

      {/* Filters section */}
      <Filters />

      {/* Miner table */}
      <MinerTable isLoaded={isLoaded} />

      {/* Mining Trends header */}
      <motion.div
        initial={{ opacity: 0, x: -30 }}
        animate={{ opacity: 1, x: 0 }}
        transition={{ duration: 0.6, delay: 0.5, type: "spring" }}
        className="relative"
      >
        <h2 className="text-3xl font-bold mb-4 bg-clip-text text-transparent bg-gradient-to-r from-blue-400 via-purple-500 to-blue-500 drop-shadow-[0_0_10px_rgba(59,130,246,0.5)]">
          Mining Trends
        </h2>
        <motion.div
          className="h-1 bg-gradient-to-r from-blue-500 to-purple-500 rounded-full w-0"
          animate={{ width: "30%", opacity: [0, 1] }}
          transition={{ delay: 0.7, duration: 0.6 }}
        />
      </motion.div>

      {/* Chart section */}
      <MiningChart isLoaded={isLoaded} />
    </div>
  );
}
