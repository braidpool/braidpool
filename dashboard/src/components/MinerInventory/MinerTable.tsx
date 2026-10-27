import React from 'react';
import { UnifiedMiner } from './Types';
import colors from '@/theme/colors';

function formatUptime(s: number): string {
  const d = Math.floor(s / 86400);
  const h = Math.floor((s % 86400) / 3600);
  const m = Math.floor((s % 3600) / 60);
  if (d > 0) return `${d}d ${h}h`;
  if (h > 0) return `${h}h ${m}m`;
  return `${m}m`;
}
function formatHashrate(thashPerSec: number): string {
  if (thashPerSec >= 1) return `${thashPerSec.toFixed(4)} TH/s`;
  const hashPerSec = thashPerSec * 1e12;
  if (hashPerSec >= 1e9) return `${(hashPerSec / 1e9).toFixed(2)} GH/s`;
  if (hashPerSec >= 1e6) return `${(hashPerSec / 1e6).toFixed(2)} MH/s`;
  if (hashPerSec >= 1e3) return `${(hashPerSec / 1e3).toFixed(2)} kH/s`;
  return `${hashPerSec.toFixed(0)} H/s`;
}

const STATUS_STYLES: Record<string, string> = {
  online: 'bg-emerald-500/10 text-emerald-300 border-emerald-500/40',
  warning: 'bg-amber-500/10 text-amber-300 border-amber-500/40',
  offline: 'bg-rose-500/10 text-rose-300 border-rose-500/40',
};

const TYPE_STYLES: Record<string, string> = {
  asic: 'bg-blue-500/10 text-blue-300 border-blue-500/40',
  cpu: 'bg-purple-500/10 text-purple-300 border-purple-500/40',
};

const DASH = '\u2014';

interface Props {
  miners: UnifiedMiner[];
  onSelect: (miner: UnifiedMiner) => void;
  onDelete: (miner: UnifiedMiner) => void;
}

const MinerTable: React.FC<Props> = ({ miners, onSelect, onDelete }) => {
  return (
    <div className="w-full overflow-x-auto">
      <div
        className="min-w-[900px] rounded-2xl bg-[#1e1e1e] p-4 border border-white/10 shadow-md"
        style={{ borderColor: colors.cardAccentSecondary }}
      >
        <div className="grid grid-cols-9 gap-2 px-4 py-3 text-xs uppercase tracking-wide text-gray-400 border-b border-gray-800/60">
          <div>Name</div>
          <div>Type</div>
          <div>Status</div>
          <div>Hashrate</div>
          <div>Shares</div>
          <div>Uptime</div>
          <div>Last Seen</div>
          <div>Actions</div>
        </div>

        <div className="divide-y divide-gray-800/40">
          {miners.map((miner) => (
            <div
              key={`${miner.type}-${miner.id}`}
              className="grid grid-cols-9 gap-4 px-4 py-3 text-sm text-gray-200 items-center hover:bg-white/[0.02] transition-colors cursor-pointer"
              onClick={() => onSelect(miner)}
            >
              <div className="font-medium text-white truncate">
                {miner.name}
              </div>
              <div>
                <span
                  className={`px-2 py-0.5 text-xs rounded border whitespace-nowrap ${TYPE_STYLES[miner.type]}`}
                >
                  {miner.type.toUpperCase()}
                </span>
              </div>
              <div>
                <span
                  className={`px-2 py-0.5 text-xs rounded border whitespace-nowrap ${STATUS_STYLES[miner.status]}`}
                >
                  {miner.status.toUpperCase()}
                </span>
              </div>

              <div className="whitespace-nowrap">
                {formatHashrate(miner.hashrateTHs)}
              </div>

              <div className="whitespace-nowrap">
                {miner.sharesAccepted !== null
                  ? `${miner.sharesAccepted} / ${miner.sharesSubmitted}`
                  : DASH}
              </div>

              <div className="whitespace-nowrap">
                {miner.uptime ? formatUptime(miner.uptime) : DASH}
              </div>

              <div className="whitespace-nowrap text-xs text-gray-400">
                {miner.lastSeen}
              </div>

              <div className="flex gap-2">
                <button
                  onClick={(e) => {
                    e.stopPropagation();
                    onDelete(miner);
                  }}
                  className="inline-flex px-3 py-1 text-xs rounded border border-rose-600/50 bg-rose-900/30 hover:bg-rose-800/50 text-rose-300 cursor-pointer transition-colors"
                  title={`Remove ${miner.name}`}
                >
                  Remove
                </button>
              </div>
              <div>
                <button
                  onClick={(e) => {
                    e.stopPropagation();
                    onSelect(miner);
                  }}
                  className="inline-flex px-3 py-1 text-xs rounded border border-gray-600 bg-gray-800/50 hover:bg-gray-700/60 text-gray-300 cursor-pointer transition-colors"
                >
                  Details
                </button>
              </div>
            </div>
          ))}
        </div>
      </div>
    </div>
  );
};

export default MinerTable;
