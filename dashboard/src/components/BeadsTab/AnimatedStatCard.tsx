import React, { useState, useRef } from 'react';
import { TrendingUp, ArrowDownRight } from 'lucide-react';
import { AnimatedStatCardProps } from './lib/types';

export default function AnimatedStatCard({
  title,
  value,
  change,
  icon,
}: AnimatedStatCardProps) {
  const cardRef = useRef(null);

  const isPositive = change.startsWith('+');
  const trendColor = isPositive
    ? 'text-emerald-400'
    : change.startsWith('-')
      ? 'text-red-400'
      : 'text-gray-400';

  return (
    <div
      ref={cardRef}
      className={`rounded-xl p-5 overflow-hidden bg-[#1c1c1c] shadow-lg hover:shadow-2xl transition-shadow`}
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
    </div>
  );
}
