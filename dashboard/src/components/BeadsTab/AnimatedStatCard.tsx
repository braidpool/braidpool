import React, { useState, useRef } from 'react';
import { motion, useInView } from 'framer-motion';
import { TrendingUp, ArrowDownRight } from 'lucide-react';

interface AnimatedStatCardProps {
  title: string;
  value: string;
  change: string;
  icon: React.ReactNode;
  delay?: number;
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
      className="rounded-xl p-5 overflow-hidden shadow-lg"
      style={{
        backgroundColor: '#1c1c1c',
        boxShadow: isHovered
          ? '0 8px 20px rgba(0, 0, 0, 0.4)'
          : '0 4px 12px rgba(0, 0, 0, 0.2)',
        transition: 'box-shadow 0.3s ease',
      }}
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
