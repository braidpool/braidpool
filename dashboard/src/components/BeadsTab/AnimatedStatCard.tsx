import type React from 'react';

import { useState, useRef } from 'react';
import { motion, useInView } from 'framer-motion';
import { TrendingUp, ArrowDownRight } from 'lucide-react';

export default function AnimatedStatCard({
  title,
  value,
  change,
  icon,
  color = 'blue',
  delay = 0,
}: {
  title: string;
  value: string;
  change: string;
  icon: React.ReactNode;
  color?: 'blue' | 'purple' | 'emerald' | 'amber';
  delay?: number;
}) {
  const cardRef = useRef(null);
  const isInView = useInView(cardRef, { once: false, amount: 0.3 });
  const [isHovered, setIsHovered] = useState(false);

  const isPositive = change?.startsWith('+');

  // Get color based on trend
  const getTrendColor = () => {
    if (isPositive) return 'text-emerald-400';
    if (!isPositive && change?.startsWith('-')) return 'text-red-400';
    return 'text-gray-400';
  };

  // Get background color based on card color
  const getBackgroundColor = () => {
    switch (color) {
      case 'blue':
        return 'bg-blue-500/20';
      case 'purple':
        return 'bg-purple-500/20';
      case 'emerald':
        return 'bg-emerald-500/20';
      case 'amber':
        return 'bg-amber-500/20';
      default:
        return 'bg-blue-500/20';
    }
  };

  // Get border gradient based on card color
  const getBorderGradient = () => {
    switch (color) {
      case 'blue':
        return 'from-blue-500/30 via-purple-500/30 to-blue-500/30';
      case 'purple':
        return 'from-purple-500/30 via-pink-500/30 to-purple-500/30';
      case 'emerald':
        return 'from-emerald-500/30 via-teal-500/30 to-emerald-500/30';
      case 'amber':
        return 'from-amber-500/30 via-orange-500/30 to-amber-500/30';
      default:
        return 'from-blue-500/30 via-purple-500/30 to-blue-500/30';
    }
  };

  return (
    <motion.div
      ref={cardRef}
      className="relative border border-gray-800/50 rounded-xl bg-black/30 backdrop-blur-md overflow-hidden p-5"
      initial={{ opacity: 0, y: 30 }}
      animate={isInView ? { opacity: 1, y: 0 } : { opacity: 0, y: 30 }}
      transition={{ duration: 0.7, delay, type: 'spring', stiffness: 100 }}
      onHoverStart={() => setIsHovered(true)}
      onHoverEnd={() => setIsHovered(false)}
    >
      {/* Animated border gradient */}
      <div className="absolute inset-0 p-[1px] rounded-xl overflow-hidden pointer-events-none">
        <motion.div
          className={`absolute inset-0 bg-gradient-to-r ${getBorderGradient()}`}
          animate={{
            backgroundPosition: ['0% 0%', '200% 0%'],
          }}
          transition={{
            duration: 8,
            repeat: Number.POSITIVE_INFINITY,
            repeatType: 'loop',
            ease: 'linear',
          }}
        />
      </div>

      {/* Hover glow effect */}
      <motion.div
        className="absolute inset-0 bg-blue-500/5 opacity-0 pointer-events-none"
        animate={{ opacity: isHovered ? 1 : 0 }}
        transition={{ duration: 0.3 }}
      />

      {/* Card content */}
      <div className="relative z-10 flex justify-between">
        <div>
          <p className="text-gray-400 text-sm">{title}</p>
          <motion.h3
            className="text-2xl font-bold text-white mt-1"
            initial={{ opacity: 0, y: 10 }}
            animate={{ opacity: 1, y: 0 }}
            transition={{ delay: delay + 0.2, duration: 0.5 }}
          >
            {value}
          </motion.h3>
          <motion.p
            className={`text-sm mt-1 flex items-center ${getTrendColor()}`}
            initial={{ opacity: 0 }}
            animate={{ opacity: 1 }}
            transition={{ delay: delay + 0.4, duration: 0.5 }}
          >
            {isPositive ? (
              <TrendingUp className="w-3 h-3 mr-1" />
            ) : (
              <ArrowDownRight className="w-3 h-3 mr-1" />
            )}
            {change} from last period
          </motion.p>
        </div>
        <motion.div
          className={`${getBackgroundColor()} p-3 rounded-lg`}
          whileHover={{ scale: 1.1, rotate: 5 }}
          animate={{ scale: [1, 1.05, 1] }}
          transition={{
            duration: 2,
            repeat: Number.POSITIVE_INFINITY,
            repeatType: 'reverse',
            delay: delay * 0.3,
          }}
        >
          {icon}
        </motion.div>
      </div>
    </motion.div>
  );
}
