import { UnifiedMiner, Miner , CpuMiner} from './Types';
import { getAlerts } from './Utils';

interface Props {
  miner: UnifiedMiner;
  onClose: () => void;
}

function formatUptime(s: number): string {
  const d = Math.floor(s / 86400);
  const h = Math.floor((s % 86400) / 3600);
  const m = Math.floor((s % 3600) / 60);
  if (d > 0) return `${d}d ${h}h ${m}m`;
  if (h > 0) return `${h}h ${m}m`;
  return `${m}m`;
}

const AsicDetails = ({ miner }: { miner: Miner }) => {
  const alerts = getAlerts(miner);
  return (
    <>
      <div className="grid grid-cols-2 gap-4">
       
        <div>
          <h3 className="text-sm font-medium text-gray-400">Firmware</h3>
          <p className="text-sm mt-1">{miner.firmware}</p>
        </div>
        <div>
          <h3 className="text-sm font-medium text-gray-400">Chip Count</h3>
          <p className="text-sm mt-1">{miner.chip_count}</p>
        </div>
        <div>
          <h3 className="text-sm font-medium text-gray-400">Voltage</h3>
          <p className="text-sm mt-1">{miner.voltage} V</p>
        </div>
        <div>
          <h3 className="text-sm font-medium text-gray-400">Temperature</h3>
          <p className="text-sm mt-1">
            {miner.temperature}
            {`\u00B0`}C (max {miner.temperature_max}
            {`\u00B0`}C)
          </p>
        </div>
        <div>
          <h3 className="text-sm font-medium text-gray-400">VR Temperature</h3>
          <p className="text-sm mt-1">
            {miner.vr_temperature}
            {`\u00B0`}C
          </p>
        </div>
        <div>
          <h3 className="text-sm font-medium text-gray-400">Power Limit</h3>
          <p className="text-sm mt-1">{miner.power_limit} W</p>
        </div>
        <div>
          <h3 className="text-sm font-medium text-gray-400">Fan Speeds</h3>
          <p className="text-sm mt-1">
            {miner.fan_speeds.length ? miner.fan_speeds.join(', ') : 'N/A'} RPM
          </p>
        </div>
      </div>

      <div className="pt-4 border-t border-gray-700">
        <h3 className="font-medium text-gray-400 mb-2">Pools</h3>
        {miner.pools.length ? (
          <ul className="text-sm space-y-1">
            {miner.pools.map((p: any, idx: number) => (
              <li key={idx}>
                {p.url || p.name || JSON.stringify(p)}
              </li>
            ))}
          </ul>
        ) : (
          <p className="text-sm text-gray-500">No pools configured</p>
        )}
      </div>

      {alerts.length > 0 && (
        <div className="pt-4 border-t border-gray-700">
          <h3 className="font-medium text-amber-300 mb-2">Alerts</h3>
          <ul className="text-sm space-y-1 text-amber-300">
            {alerts.map((a, idx) => (
              <li key={idx}>{a.message}</li>
            ))}
          </ul>
        </div>
      )}

      {miner.errors.length > 0 && (
        <div className="pt-4 border-t border-gray-700">
          <h3 className="font-medium text-rose-300 mb-2">Errors</h3>
          <ul className="text-sm space-y-1 text-rose-300">
            {miner.errors.map((e: any, idx: number) => (
              <li key={idx}>{typeof e === 'string' ? e : JSON.stringify(e)}</li>
            ))}
          </ul>
        </div>
      )}
    </>
  );
};

const CpuDetails = ({ miner }: { miner: CpuMiner }) => {
  const stats = miner.stats;
  if (!stats) {
    return <p className="text-sm text-gray-500">No stats reported yet.</p>;
  }
  return (
    <>
      <div className="grid grid-cols-2 gap-4">
        <div>
          <h3 className="text-sm font-medium text-gray-400">API URL</h3>
          <p className="text-sm mt-1 break-all">{miner.api_url}</p>
        </div>
        <div>
          <h3 className="text-sm font-medium text-gray-400">Miner Version</h3>
          <p className="text-sm mt-1">{stats.minerVersion}</p>
        </div>
        <div>
          <h3 className="text-sm font-medium text-gray-400">Threads</h3>
          <p className="text-sm mt-1">{stats.hashrate.threads}</p>
        </div>
        <div>
          <h3 className="text-sm font-medium text-gray-400">Total Hashes</h3>
          <p className="text-sm mt-1">
            {stats.hashrate.totalHashes.toLocaleString()}
          </p>
        </div>
      </div>

      <div className="pt-4 border-t border-gray-700">
        <h3 className="font-medium text-gray-400 mb-2">Connection</h3>
        <div className="text-sm space-y-1">
          <p>
            <strong>Status:</strong> {stats.connection.status}
          </p>
          <p>
            <strong>Pool:</strong> {stats.connection.poolUrl}
          </p>
          <p>
            <strong>Username:</strong> {stats.connection.username}
          </p>
          <p>
            <strong>Difficulty:</strong> {stats.connection.difficulty}
          </p>
        </div>
      </div>

      <div className="pt-4 border-t border-gray-700">
        <h3 className="font-medium text-gray-400 mb-2">Worker Threads</h3>
        {stats.workerThreads.length ? (
          <ul className="text-sm space-y-1">
            {stats.workerThreads.map((w) => (
              <li key={w.id}>
                Thread {w.id}: {w.status}
              </li>
            ))}
          </ul>
        ) : (
          <p className="text-sm text-gray-500">No worker data</p>
        )}
      </div>

      <div className="pt-4 border-t border-gray-700">
        <h3 className="font-medium text-gray-400 mb-2">Recent Shares</h3>
        {stats.recentShares.length ? (
          <ul className="text-sm space-y-1">
            {stats.recentShares.slice(0, 10).map((s, idx) => (
              <li key={idx} className="break-all">
                {new Date(s.timestamp).toLocaleTimeString()} — job {s.jobId} —{' '}
                {s.accepted === null
                  ? 'pending'
                  : s.accepted
                    ? 'accepted'
                    : 'rejected'}
              </li>
            ))}
          </ul>
        ) : (
          <p className="text-sm text-gray-500">No recent shares</p>
        )}
      </div>
    </>
  );
};

const MinerDetailsDialog = ({ miner, onClose }: Props) => {
  return (
    <>
      <div
        className="fixed inset-0 z-40"
        onClick={onClose}
        data-testid="overlay"
      />

      <div className="fixed right-0 top-14 z-50 h-[calc(100%-3.5rem)] w-full max-w-md sm:w-96 bg-[#1e1e1e] overflow-y-auto shadow-2xl text-white border border-gray-700">
        <div className="sticky top-0 border-white bg-[#1e1e1e] p-4 flex justify-between items-center">
          <h2 className="text-lg font-bold">Miner Details</h2>
          <button
            onClick={onClose}
            className="text-gray-400 hover:text-white p-1 rounded-full hover:border-white/10 bg-[#1e1e1e]"
            aria-label="Close dialog"
          >
            ✕
          </button>
        </div>

        <div className="p-4 space-y-4">
          <div>
            <h3 className="text-sm font-medium text-gray-400">Uptime</h3>
            <p className="text-sm mt-1">{formatUptime(miner.uptime)}</p>
          </div>

          {miner.type === 'asic' ? (
            <AsicDetails miner={miner.raw as Miner} />
          ) : (
            <CpuDetails miner={miner.raw as CpuMiner} />
          )}
        </div>
      </div>
    </>
  );
};

export default MinerDetailsDialog;
