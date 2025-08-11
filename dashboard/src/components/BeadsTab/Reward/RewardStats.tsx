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
  <div className=" p-4 rounded-lg border border-gray-600">
    <h3 className="text-gray-300 text-sm font-medium mb-2">{title}</h3>
    <div className="space-y-1">
      <div className="text-white text-lg font-semibold">
        {formatValue(btcValue, 'BTC')} BTC
      </div>
      <div className="text-white text-xs  font-semibold  overflow-x-hidden">
        ${formatValue(usdValue, 'USD')}
      </div>
      {blocks !== undefined && timeframe && (
        <div className="text-gray-400 text-xs">
          {blocks} blocks {timeframe}
        </div>
      )}
    </div>
  </div>
);
