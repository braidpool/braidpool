import React, { useState, useRef } from 'react';
import { motion, useInView } from 'framer-motion';
import { TrendingUp, ArrowDownRight } from 'lucide-react';

interface AnimatedStatCardProps {
  title: string;
  value: string;
  change: string;
  icon: React.ReactNode;
  delay?: number;
  color?: string;
}

export default function AnimatedStatCard({
  title,
  value,
  change,
  icon,
  delay = 0,
}: AnimatedStatCardProps) {
  const cardRef = useRef(null);
  const isInView = useInView(cardRef, { once: false, amount: 0.3 });
  const [isHovered, setIsHovered] = useState(false);
  const isPositive = change.startsWith('+');
  const trendColor = isPositive
    ? 'text-emerald-400'
    : change.startsWith('-')
      ? 'text-red-400'
      : 'text-gray-400';

  return (
    <motion.div
      ref={cardRef}
      className={`rounded-xl p-5 overflow-hidden bg-[#1c1c1c] shadow-lg hover:shadow-2xl transition-shadow`}
      initial={{ opacity: 0, y: 30 }}
      animate={isInView ? { opacity: 1, y: 0 } : { opacity: 0, y: 30 }}
      transition={{ duration: 0.6, delay }}
      onMouseEnter={() => setIsHovered(true)}
      onMouseLeave={() => setIsHovered(false)}
    >
      <div className="flex justify-between items-start">
        <div>
          <p className="text-gray-400 text-sm">{title}</p>
          <h3 className="text-white text-2xl font-bold mt-1">{value}</h3>
          <p className={`text-sm mt-1 flex items-center ${trendColor}`}>
            {isPositive ? (
              <TrendingUp className="w-4 h-4 mr-1" />
            ) : (
              <ArrowDownRight className="w-4 h-4 mr-1" />
            )}
            {change} from last period
          </p>
        </div>
        <div className="bg-white/5 p-3 rounded-lg">{icon}</div>
      </div>
    </motion.div>
  );
}
