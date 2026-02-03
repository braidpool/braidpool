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
  accentColor = 'var(--color-primary)',
  headerExtra,
}) => {
  return (
    <div className="relative px-3 rounded border border-border overflow-hidden h-full shadow-sm pb-3 bg-paper">
      {/* Accent color border */}
      {accentColor && (
        <div
          className="absolute top-0 left-0 w-1 h-full"
          style={{ backgroundColor: accentColor }}
        />
      )}

      {/* Header section */}
      {(title || subtitle || headerExtra) && (
        <div className="px-3 py-3 border-b border-border flex justify-between items-center bg-paper">
          <div>
            {title && (
              <h3 className="text-base font-medium text-textPrimary">
                {title}
              </h3>
            )}
            {subtitle && (
              <p className="text-xs text-textSecondary">{subtitle}</p>
            )}
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
