import { useState, useEffect } from 'react';
import { Miner } from './Types';
import { DeviceCard } from './Card';
import { API_URLS } from '../../URLs';
const MinerInventoryDashboard = () => {
  const [miners, setMiners] = useState<Miner[]>([]);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [newMinerIP, setNewMinerIP] = useState('');
  const [autoRefresh, setAutoRefresh] = useState(true);
  const [refreshInterval, setRefreshInterval] = useState(30);
  const [lastUpdate, setLastUpdate] = useState<Date | null>(null);

  // Helper functions
  const determineStatus = (data: any): 'online' | 'warning' | 'offline' => {
    if (!data.is_mining || (data.hashrate_current || 0) === 0) return 'offline';
    if (
      (data.temperature || 0) > 80 ||
      (data.vr_temperature || 0) > 85 ||
      data.errors?.length > 0
    )
      return 'warning';
    return 'online';
  };

  const countAlerts = (data: any): number => {
    let alerts = 0;
    if ((data.temperature || 0) > 80) alerts++;
    if ((data.vr_temperature || 0) > 85) alerts++;
    if (!data.is_mining) alerts++;
    if (data.errors && data.errors.length > 0) alerts += data.errors.length;
    return alerts;
  };

  const fetchMinerData = async (ip: string): Promise<Miner | null> => {
    try {
      const response = await fetch(
        `${API_URLS.MINER_DEVICE_URL}/api/miners?ip=${ip}`,
        {
          headers: { Accept: 'application/json' },
        }
      );

      const responseData = await response.json();

      if (!response.ok || !responseData.success) {
        console.error(`Failed to fetch data for ${ip}:`, responseData.error);
        return null;
      }

      const data = responseData.data;

      const miner: Miner = {
        id: data.mac || ip + '_' + Date.now(),
        ip: data.ip || ip,
        hostname: data.hostname || 'Unknown',
        mac: data.mac || 'Unknown',
        make: data.make || 'Unknown',
        model: data.model || 'Unknown',
        firmware: data.firmware || 'Unknown',

        status: determineStatus(data),
        is_mining: data.is_mining || false,
        uptime: data.uptime || 0,
        errors: data.errors || [],
        alerts: countAlerts(data),
        lastSeen: new Date().toLocaleTimeString(),

        hashrate_current: data.hashrate_current || 0,
        hashrate_avg: data.hashrate_avg || 0,
        expected_hashrate: data.expected_hashrate || 0,

        temperature: data.temperature || 0,
        temperature_max: data.temperature_max || 0,
        vr_temperature: data.vr_temperature || 0,

        power_usage: data.power_usage || 0,
        power_limit: data.power_limit || 0,
        efficiency: data.efficiency || 0,
        voltage: data.voltage || 0,

        fan_speeds: data.fan_speeds || [],
        chip_count: data.chip_count || 0,

        primary_pool: data.primary_pool || 'No Pool',
        pools: data.pools || [],
      };

      return miner;
    } catch (err) {
      console.error(`Error fetching data for ${ip}:`, err);
      return null;
    }
  };

  const refreshAllMiners = async () => {
    if (miners.length === 0) return;

    setLoading(true);
    const updatedMiners: Miner[] = [];

    for (const miner of miners) {
      const updatedMiner = await fetchMinerData(miner.ip);
      if (updatedMiner) {
        updatedMiner.id = miner.id;
        updatedMiners.push(updatedMiner);
      } else {
        updatedMiners.push({
          ...miner,
          status: 'offline' as const,
          lastSeen: new Date().toLocaleTimeString(),
          alerts: miner.alerts + 1,
        });
      }
    }

    setMiners(updatedMiners);
    setLastUpdate(new Date());
    setLoading(false);
  };

  useEffect(() => {
    if (!autoRefresh || miners.length === 0) return;

    const interval = setInterval(refreshAllMiners, refreshInterval * 1000);
    return () => clearInterval(interval);
  }, [autoRefresh, refreshInterval, miners.length]);

  const addMinerByIP = async () => {
    if (!newMinerIP.trim()) {
      setError('Please enter a valid IP address');
      return;
    }

    setLoading(true);
    setError(null);

    const newMiner = await fetchMinerData(newMinerIP.trim());

    if (newMiner) {
      setMiners((prev) => {
        const exists = prev.find((m) => m.ip === newMiner.ip);
        if (exists) {
          return prev.map((m) =>
            m.ip === newMiner.ip ? { ...newMiner, id: m.id } : m
          );
        }
        return [...prev, newMiner];
      });
      setNewMinerIP('');
      setLastUpdate(new Date());
    } else {
      const errorMsg = `Could not connect to miner at ${newMinerIP.trim()}`;
      setError(errorMsg);
    }

    setLoading(false);
  };

  const totalMiners = miners.length;
  const onlineMiners = miners.filter((m) => m.status === 'online').length;
  const warningMiners = miners.filter((m) => m.status === 'warning').length;
  const offlineMiners = miners.filter((m) => m.status === 'offline').length;
  const totalHashrate = miners.reduce(
    (sum, m) => sum + (m.hashrate_current || 0),
    0
  );
  const totalPower = miners.reduce((sum, m) => sum + (m.power_usage || 0), 0);
  const avgEfficiency =
    totalMiners > 0
      ? (miners.reduce((sum, m) => sum + (m.efficiency || 0), 0) /
          totalMiners) *
        1000
      : 0;

  return (
    <div className="min-h-screen  text-white p-6">
      <div className="text-center mb-8">
        <h1 className="text-3xl font-bold text-white mb-2">
          {' '}
          Mining Dashboard
        </h1>

        {error && (
          <div className="text-red-400 border  px-4 py-3 rounded mt-4 max-w-md mx-auto ">
            <strong className="font-bold">Error: </strong>
            <span className="block sm:inline">{error}</span>
          </div>
        )}

        <div className="flex justify-center items-center gap-2 mt-4 flex-wrap ">
          <input
            type="text"
            value={newMinerIP}
            onChange={(e) => setNewMinerIP(e.target.value)}
            placeholder="Enter Miner IP "
            className="px-3 py-2 text-sm border border-gray-600 bg-gray-800 rounded text-white placeholder-gray-400 w-64"
            onKeyPress={(e) => e.key === 'Enter' && addMinerByIP()}
          />
          <button
            onClick={addMinerByIP}
            disabled={loading}
            className="px-4 py-2 text-sm  text-white rounded bg-gray-800"
          >
            {loading ? 'Adding...' : 'Add Miner'}
          </button>
        </div>

        {/* Summary Stats */}
        <div className="flex flex-wrap justify-center gap-3 mt-6 text-sm">
          <div className="px-4 py-2 rounded-md border border-gray-600 text-gray-400 ">
            {onlineMiners} Online
          </div>
          <div className="px-4 py-2 rounded-md border border-gray-600 text-gray-400">
            {warningMiners} Warning
          </div>
          <div className="px-4 py-2 rounded-md border border-gray-600 text-gray-400">
            {offlineMiners} Offline
          </div>
          <div className="px-4 py-2 rounded-md border border-gray-600 text-gray-400 ">
            Total Miner : {totalMiners} Total
          </div>
          <div className="px-4 py-2 rounded-md border border-gray-600 text-gray-400 ">
            Total Hashrate : {totalHashrate.toFixed(3)} TH/s Total
          </div>
          <div className="px-4 py-2 rounded-md border border-gray-600 text-gray-400 ">
            Total Power: {totalPower}W Total
          </div>
          <div className="px-4 py-2 rounded-md border border-gray-600 text-gray-400 ">
            Total Efficiency : {avgEfficiency.toFixed(1)} W/TH Avg
          </div>
        </div>
      </div>

      {miners.length === 0 ? (
        <div className="text-center py-12 text-gray-400">
          <p className="text-lg">No miners found</p>
          <p className="text-sm mt-2">
            Add your miner by entering its IP address above
          </p>
        </div>
      ) : (
        <div className="flex overflow-x-auto space-x-4 pb-4">
          {miners.map((miner) => (
            <DeviceCard key={miner.id} miner={miner} />
          ))}
        </div>
      )}
    </div>
  );
};

export default MinerInventoryDashboard;
