import React, { useState } from 'react';
import { MinerTableProps } from './Types';
import colors from '@/theme/colors';

function formatUptime(s: number): string {
  const d = Math.floor(s / 86400);
  const h = Math.floor((s % 86400) / 3600);
  const m = Math.floor((s % 3600) / 60);
  if (d > 0) return `${d}d ${h}h`;
  if (h > 0) return `${h}h ${m}m`;
  return `${m}m`;
}

const STATUS_STYLES: Record<string, string> = {
  online: 'bg-emerald-500/10 text-emerald-300 border-emerald-500/40',
  warning: 'bg-amber-500/10 text-amber-300 border-amber-500/40',
  offline: 'bg-rose-500/10 text-rose-300 border-rose-500/40',
};

const MinerTable: React.FC<MinerTableProps> = ({
  miners,
  getAlerts,
  onDelete,
}) => {
  const [expandedAlerts, setExpandedAlerts] = useState<Record<string, boolean>>(
    {}
  );
  const hasAlerts = miners.some((m) => getAlerts(m).length > 0);

  return (
    <div className="w-full overflow-x-auto">
      <div
        className="min-w-[800px] rounded-2xl bg-[#1e1e1e] p-4 border border-white/10 shadow-md"
        style={{ borderColor: colors.cardAccentSecondary }}
      >
        {/* Header row */}
        <div
          className={`grid ${hasAlerts ? 'grid-cols-10' : 'grid-cols-9'} gap-4 px-4 py-3 text-xs uppercase tracking-wide text-gray-400 border-b border-gray-800/60`}
        >
          <div>Model</div>
          <div>Hashrate</div>
          <div>Efficiency</div>
          <div>Power </div>
          <div>Status</div>
          {hasAlerts && <div>Alerts</div>}
          <div>Temp</div>
          <div>Pool</div>
          <div>Uptime</div>
          <div>Actions</div>
        </div>

        {/* Miner rows */}
        <div className="divide-y divide-gray-800/40">
          {miners.map((miner) => {
            const alerts = getAlerts(miner);
            const isExpanded = expandedAlerts[miner.id] || false;
            const firstAlert = alerts[0];
            const remainingCount = alerts.length - 1;
            const pool = miner.pools?.[0];

            return (
              <div
                key={miner.id}
                className={`grid ${hasAlerts ? 'grid-cols-10' : 'grid-cols-9'} gap-4 px-4 py-3 text-sm text-gray-200 items-start hover:bg-white/[0.02] transition-colors`}
              >
                <div>
                  <div className="font-medium text-white truncate">
                    {[miner.make, miner.model]
                      .filter((v) => v && v !== 'Unknown')
                      .join(' ') ||
                      (miner.hostname !== 'Unknown'
                        ? miner.hostname
                        : 'Unknown')}
                  </div>
                </div>

                {/* Hashrate */}
                <div>
                  <div className="whitespace-nowrap">
                    {(miner.hashrate_current || 0).toFixed(2)} TH/s
                  </div>
                  <div className="text-xs text-gray-500 mt-0.5">
                    {(miner.expected_hashrate || 0).toFixed(2)} exp
                  </div>
                </div>

                {/* Efficiency */}
                <div className="whitespace-nowrap">
                  {miner.efficiency
                    ? `${miner.efficiency.toFixed(1)} J/TH`
                    : 'NA'}
                </div>

                {/* Power / Uptime */}
                <div>
                  <div className="whitespace-nowrap">
                    {miner.power_usage || 0} W
                  </div>
                </div>

                {/* Status */}
                <div>
                  <span
                    className={`px-2 py-0.5 text-xs rounded border whitespace-nowrap ${STATUS_STYLES[miner.status] ?? ''}`}
                  >
                    {miner.status.toUpperCase()}
                  </span>
                </div>

                {/* Alerts  */}
                {hasAlerts &&
                  (alerts.length > 0 ? (
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
                        <div className="flex items-center gap-2 px-2.5 py-1.5 rounded-md border text-xs font-medium bg-gray-800/60 border-gray-700/40 text-amber-300 hover:bg-gray-800/80">
                          <span>{firstAlert.message}</span>
                          {remainingCount > 0 && (
                            <span className="px-1.5 py-0.5 rounded bg-gray-700/50 text-gray-400 text-[10px]">
                              +{remainingCount}
                            </span>
                          )}
                          <span className="ml-auto text-gray-500 text-[10px]">
                            {isExpanded ? '\u25B2' : '\u25BC'}
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
                    <div />
                  ))}

                {/* Temperature */}
                <div className="text-gray-300">
                  <div className="whitespace-nowrap">
                    {miner.temperature || 0}
                    {`\u00B0`}C{' '}
                    <span className="text-gray-500 text-xs">ASIC</span>
                  </div>
                </div>

                {/* Pool / Worker */}
                <div>
                  {miner.primary_pool && miner.primary_pool !== 'No Pool' ? (
                    <>
                      <div className="text-sm text-gray-200">
                        {miner.primary_pool}
                        {pool?.user ? ` | ${pool.user}` : ''}
                      </div>
                    </>
                  ) : (
                    <span className="text-gray-600">{'\u2014'}</span>
                  )}
                </div>
                {/* Uptime */}
                <div>
                  {miner.uptime ? (
                    <div className="text-sm text-gray-200">
                      {formatUptime(miner.uptime)}
                    </div>
                  ) : null}
                </div>
                {/* Remove */}
                <div>
                  {onDelete && (
                    <button
                      onClick={() => onDelete(miner.id)}
                      className="inline-flex px-3 py-1 text-xs rounded border border-rose-600/50 bg-rose-900/30 hover:bg-rose-800/50 text-rose-300 cursor-pointer transition-colors"
                      title={`Remove ${miner.ip}`}
                    >
                      X
                    </button>
                  )}
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
