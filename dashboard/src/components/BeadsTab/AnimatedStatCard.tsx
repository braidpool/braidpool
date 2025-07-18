import { useRef } from 'react';
import { AnimatedStatCardProps } from './lib/Types';

export default function AnimatedStatCard({
  title,
  value,
}: AnimatedStatCardProps) {
  const cardRef = useRef(null);
  return (
    <div
      ref={cardRef}
      className={`rounded-xl p-5 overflow-hidden bg-[#1c1c1c] border border-gray-700  backdrop-blur-sm shadow-lg hover:shadow-2xl transition-shadow`}
    >
      <div className="flex justify-between items-start">
        <div>
          <p className="text-gray-400 text-sm">{title}</p>
          <h3 className="text-white text-sm font-bold mt-1">{value}</h3>
        </div>
      </div>
    </div>
  );
}
