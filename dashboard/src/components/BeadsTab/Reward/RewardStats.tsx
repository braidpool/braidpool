import { formatValue } from '../lib/Utils';
export const StatCard = ({
  title,
  btcValue,
  usdValue,
  blocks,
  timeframe,
}: {
  title: string;
  btcValue: number;
  usdValue: number;
  blocks?: number;
  timeframe?: string;
}) => (
  <div className="bg-paper p-4 rounded-lg border border-gray-600">
    <h3 className="text-textSecondary text-sm font-medium mb-2">{title}</h3>
    <div className="space-y-1">
      <div className="text-textPrimary text-lg font-semibold">
        {formatValue(btcValue, 'BTC')} BTC
      </div>
      <div className="text-textPrimary text-xs font-semibold overflow-x-hidden">
        ${formatValue(usdValue, 'USD')}
      </div>
      {blocks !== undefined && timeframe && (
        <div className="text-textSecondary text-xs">
          {blocks} blocks {timeframe}
        </div>
      )}
    </div>
  </div>
);
