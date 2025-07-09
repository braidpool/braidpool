import React from 'react';
import { CardProps } from './Types';

/**
 * A reusable card component with a standard styling pattern
 * used throughout the dashboard
 */
const Card: React.FC<CardProps> = ({
  title,
  subtitle,
  children,
  accentColor = '#1976d2',
  headerExtra,
}) => {
  return (
    <div
      className="relative px-3 rounded border border-black/5 overflow-hidden h-full shadow-sm pb-3"
      style={{ backgroundColor: 'rgba(30, 30, 30, 1)' }}
    >
      {/* Accent color border */}
      {accentColor && (
        <div
          className="absolute top-0 left-0 w-1 h-full"
          style={{ backgroundColor: accentColor }}
        />
      )}

      {/* Header section */}
      {(title || subtitle || headerExtra) && (
        <div className="px-3 py-3 border-b border-black/5 flex justify-between items-center bg-black/[0.01]">
          <div>
            {title && (
              <h3 className="text-base font-medium text-white">{title}</h3>
            )}
            {subtitle && <p className="text-xs text-gray-300">{subtitle}</p>}
          </div>
          {headerExtra && <div>{headerExtra}</div>}
        </div>
      )}

      {/* Content */}
      <div className="p-0">{children}</div>
    </div>
  );
};

export default Card;
