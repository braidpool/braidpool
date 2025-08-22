import { Miner } from './Types';
export const DeviceCard = ({ miner }: { miner: Miner }) => {
  const getStatusColor = (status: string) => {
    switch (status) {
      case 'online':
        return 'bg-green-500';
      case 'warning':
        return 'bg-yellow-400';
      case 'offline':
        return 'bg-red-500';
      default:
        return 'bg-gray-500';
    }
  };

  const formatUptime = (seconds: number): string => {
    if (!seconds) return '0m';
    const days = Math.floor(seconds / 86400);
    const hours = Math.floor((seconds % 86400) / 3600);
    const minutes = Math.floor((seconds % 3600) / 60);

    if (days > 0) return `${days}d ${hours}h`;
    if (hours > 0) return `${hours}h ${minutes}m`;
    return `${minutes}m`;
  };

  const statusColor = getStatusColor(miner.status);
  const displayName =
    miner.hostname || `${miner.make} ${miner.model}` || 'Unknown Miner';
  const primaryFanSpeed = miner.fan_speeds?.[0] || 0;

  return (
    <div className="relative w-full max-w-[400px] border border-gray-700 rounded-xl p-5 backdrop-blur-sm transition-transform duration-200 hover:-translate-y-1 hover:shadow-xl bg-gray-800/50">
      <div
        className={`absolute top-3 right-3 w-3 h-3 rounded-full ${statusColor}`}
      />

      {miner.alerts > 0 && (
        <div className="absolute top-2 right-10 px-2 py-0.5 text-xs rounded-full bg-red-100 dark:bg-red-900 text-red-700 dark:text-red-300">
          ⚠ {miner.alerts}
        </div>
      )}

      <div className="flex items-center justify-between mb-3">
        <h3 className="text-lg font-semibold text-white">{displayName}</h3>
        {miner.is_mining && (
          <span className="text-xs bg-green-600 text-white px-2 py-1 rounded">
            MINING
          </span>
        )}
      </div>

      <div className="flex justify-between text-xs text-gray-400 mb-3">
        <span>
          Model: {miner.make} {miner.model}
        </span>
        <span>Last Seen: {miner.lastSeen}</span>
      </div>

      <div className="text-sm text-gray-300 space-y-2 mb-4">
        <div className="flex justify-between">
          <span>
            Hashrate:{' '}
            <span className="text-white">
              {(miner.hashrate_current || 0).toFixed(3)} TH/s
            </span>
          </span>
          <span>
            Expected: {(miner.expected_hashrate || 0).toFixed(3)} TH/s
          </span>
        </div>

        <div className="flex justify-between">
          <span>Pool: {miner.primary_pool}</span>
          <span>Firmware: {miner.firmware || 'Unknown'}</span>
        </div>

        <div className="flex justify-between">
          <span>
            Power:{' '}
            <span className="text-white">{miner.power_usage || 0} W</span>
          </span>
          <span>Uptime: {formatUptime(miner.uptime)}</span>
        </div>

        <div className="flex justify-between">
          <span>
            ASIC Temp:{' '}
            <span
              className={
                miner.temperature > 80
                  ? 'text-red-400'
                  : miner.temperature > 70
                    ? 'text-yellow-400'
                    : 'text-white'
              }
            >
              {miner.temperature || 0}°C
            </span>
          </span>
          <span>
            VR Temp:{' '}
            <span
              className={
                miner.vr_temperature > 85
                  ? 'text-red-400'
                  : miner.vr_temperature > 75
                    ? 'text-yellow-400'
                    : 'text-white'
              }
            >
              {miner.vr_temperature || 0}°C
            </span>
          </span>
        </div>

        <div className="flex justify-between">
          <span>Fan Speed: {primaryFanSpeed} RPM</span>
          <span>
            Efficiency: {((miner.efficiency || 0) * 1000).toFixed(1)} W/TH
          </span>
        </div>

        <div className="flex justify-between">
          <span>Chips: {miner.chip_count || 0}</span>
          <span>
            Voltage: {miner.voltage ? `${miner.voltage.toFixed(0)}mV` : 'N/A'}
          </span>
        </div>
      </div>

      <div className="flex justify-between items-center mt-3 pt-3 border-t border-gray-700">
        <div className="text-xs text-gray-400">
          Performance:{' '}
          {miner.expected_hashrate
            ? Math.round(
                (miner.hashrate_current / miner.expected_hashrate) * 100
              )
            : 0}
          %
        </div>
      </div>
    </div>
  );
};
