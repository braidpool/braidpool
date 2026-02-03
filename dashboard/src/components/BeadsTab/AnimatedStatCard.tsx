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
      className={`rounded-xl p-5 overflow-hidden border border-border backdrop-blur-sm shadow-lg hover:shadow-2xl transition-shadow bg-paper`}
    >
      <div className="flex justify-between items-start">
        <div>
          <p className="text-textSecondary text-sm">{title}</p>
          <h3 className="text-textPrimary text-sm font-bold mt-1">{value}</h3>
        </div>
      </div>
    </div>
  );
}
