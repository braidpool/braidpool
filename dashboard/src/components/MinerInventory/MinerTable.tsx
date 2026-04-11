import React from 'react';
import { Link } from 'react-router-dom';
import { MinerTableProps } from './Types';
import colors from '@/theme/colors';

const MinerTable: React.FC<MinerTableProps> = ({
  miners,
  minerHistory,
  getAlerts,
  expandedAlerts,
  setExpandedAlerts,
  statusStyles,
}) => {
  const hasAlerts = miners.some((m) => getAlerts(m).length > 0);

  return (
    <div className="w-full overflow-x-auto">
      <div
        className="min-w-[800px] rounded-2xl bg-[#1e1e1e] p-4 border border-white/10 shadow-md"
        style={{ borderColor: colors.cardAccentSecondary }}
      >
        <div
          className={`grid ${hasAlerts ? 'grid-cols-8' : 'grid-cols-7'} gap-4 px-4 py-3 text-xs uppercase tracking-wide text-gray-400 border-b border-gray-800/60`}
        >
          <div>Model</div>
          <div>Hashrate</div>
          <div>Efficiency</div>
          <div>Power</div>
          <div>Status</div>
          {hasAlerts && <div>Alerts</div>}
          <div>Temp</div>
          <div>Details</div>
        </div>
        <div className="rounded-2xl   shadow-md p-4">
          {miners.map((miner) => {
            const alerts = getAlerts(miner);
            const isExpanded = expandedAlerts[miner.id] || false;
            const firstAlert = alerts[0];
            const remainingCount = alerts.length - 1;
            return (
              <div
                key={miner.id}
                className={`grid ${hasAlerts ? 'grid-cols-8' : 'grid-cols-7'} gap-4 px-4 py-3 text-sm text-gray-200 items-center`}
              >
                <div className="font-medium text-white truncate">
                  {miner.hostname ||
                    (miner.make || miner.model
                      ? [miner.make, miner.model].filter(Boolean).join(' ')
                      : 'Unknown')}
                </div>
                <div className="whitespace-nowrap">
                  {(miner.hashrate_current || 0).toFixed(3)} TH/s
                </div>
                <div className="whitespace-nowrap">
                  {(miner.efficiency || 0).toFixed(1)} W/TH
                </div>
                <div className="whitespace-nowrap">
                  {miner.power_usage || 0} W
                </div>
                <div>
                  <span
                    className={`px-2 py-0.5 text-xs rounded border whitespace-nowrap ${statusStyles[miner.status]}`}
                  >
                    {miner.status.toUpperCase()}
                  </span>
                </div>
                {hasAlerts && alerts.length > 0 ? (
                  <div className="flex flex-col gap-1.5">
                    <div
                      className="cursor-pointer select-none"
                      onClick={() =>
                        setExpandedAlerts((prev) => ({
                          ...prev,
                          [miner.id]: !prev[miner.id],
                        }))
                      }
                    >
                      <div className="flex items-center gap-2 px-2.5 py-1.5 rounded-md border text-xs font-medium transition-colors bg-gray-800/60 border-gray-700/40 text-amber-300 hover:bg-gray-800/80">
                        <span>{firstAlert.message}</span>
                        {remainingCount > 0 && (
                          <span className="px-1.5 py-0.5 rounded bg-gray-700/50 text-gray-400 text-[10px]">
                            +{remainingCount}
                          </span>
                        )}
                        <span className="ml-auto text-gray-500 text-[10px]">
                          {isExpanded ? '▲' : '▼'}
                        </span>
                      </div>
                    </div>
                    {isExpanded && alerts.length > 1 && (
                      <div className="flex flex-col gap-1 pl-2 border-l-2 text-amber-300 border-gray-700/50">
                        {alerts.slice(1).map((alert, idx) => (
                          <div key={idx}>{alert.message}</div>
                        ))}
                      </div>
                    )}
                  </div>
                ) : (
                  hasAlerts && <div></div>
                )}
                <div className="text-gray-300 whitespace-nowrap">
                  {miner.temperature || 0}°C / {miner.vr_temperature || 0}°C
                </div>
                <div className="text-gray-300 whitespace-nowrap">
                  <Link
                    to="#"
                    onClick={(e) => e.preventDefault()}
                    className={`inline-flex px-3 py-1 text-xs rounded border ${
                      minerHistory[miner.id] &&
                      minerHistory[miner.id].length > 1
                        ? 'border-gray-600 bg-gray-800 hover:bg-gray-700 cursor-pointer'
                        : 'border-gray-700 bg-gray-900 text-gray-500 cursor-not-allowed'
                    }`}
                    title={
                      minerHistory[miner.id] &&
                      minerHistory[miner.id].length > 1
                        ? 'View detailed analytics'
                        : 'Collecting data... Please wait'
                    }
                  >
                    Details
                  </Link>
                </div>
              </div>
            );
          })}
        </div>
      </div>
    </div>
  );
};

export default MinerTable;
