import { useState, useEffect, useRef } from 'react';
import { Miner } from './Types';
import { DeviceCard } from './Card';
import { API_URLS } from '../../URLs';
const MinerInventoryDashboard = () => {
  const [miners, setMiners] = useState<Miner[]>([]);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [newMinerIP, setNewMinerIP] = useState('');
  const [autoRefresh, setAutoRefresh] = useState(true);
  const [searchInput, setSearchInput] = useState('');
  const [searchQuery, setSearchQuery] = useState('');
  const [sortBy, setSortBy] = useState<
    'all' | 'efficiency' | 'hashrate' | 'power' | 'temperature'
  >('all');
  const [statusFilter, setStatusFilter] = useState<
    'all' | 'online' | 'warning' | 'offline'
  >('all');
  const [refreshInterval, setRefreshInterval] = useState(30);
  const [lastUpdate, setLastUpdate] = useState<Date | null>(null);
  const minersRef = useRef<Miner[]>([]);

  useEffect(() => {
    minersRef.current = miners;
  }, [miners]);

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
    const currentMiners = minersRef.current;
    if (currentMiners.length === 0) return;

    setLoading(true);

    const results = await Promise.all(
      currentMiners.map((m) => fetchMinerData(m.ip).catch(() => null))
    );

    const updatedMiners: Miner[] = results.map((updated, idx) => {
      const orig = currentMiners[idx];
      if (updated) {
        updated.id = orig.id;
        return updated;
      }
      return {
        ...orig,
        status: 'offline' as const,
        lastSeen: new Date().toLocaleTimeString(),
        alerts: (orig.alerts || 0) + 1,
      };
    });

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

  const handleSearch = () => setSearchQuery(searchInput.trim());
  const clearSearch = () => {
    setSearchInput('');
    setSearchQuery('');
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

  const displayedMiners =
    !searchQuery || searchQuery.length === 0
      ? miners
      : miners.filter((m) => {
          const q = searchQuery.toLowerCase();
          return (
            (m.ip || '').toLowerCase().includes(q) ||
            (m.hostname || '').toLowerCase().includes(q)
          );
        });

  // Apply status filter
  const filteredByStatus =
    statusFilter === 'all'
      ? displayedMiners
      : displayedMiners.filter((m) => m.status === statusFilter);

  // Apply sorting to the filtered list
  const sortedDisplayedMiners = (() => {
    const arr = [...filteredByStatus];
    if (sortBy === 'all') return arr;

    arr.sort((a, b) => {
      switch (sortBy) {
        case 'efficiency':
          return (b.efficiency || 0) - (a.efficiency || 0);
        case 'hashrate':
          return (b.hashrate_current || 0) - (a.hashrate_current || 0);
        case 'power':
          return (b.power_usage || 0) - (a.power_usage || 0);
        case 'temperature':
          return (b.temperature || 0) - (a.temperature || 0);
        default:
          return 0;
      }
    });

    return arr;
  })();

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
            placeholder="Enter Miner IP"
            aria-label="Miner IP"
            className="px-3 py-2 text-sm border border-gray-600 bg-gray-800 rounded text-white placeholder-gray-400 w-64"
            onKeyDown={(e) => e.key === 'Enter' && addMinerByIP()}
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
          <button
            onClick={() =>
              setStatusFilter((s) => (s === 'online' ? 'all' : 'online'))
            }
            className={
              'px-4 py-2 rounded-md border transition text-sm ' +
              (statusFilter === 'online'
                ? 'border-blue-400 text-white bg-gray-700'
                : 'border-gray-600 text-gray-400')
            }
          >
            {onlineMiners} Online
          </button>
          <button
            onClick={() =>
              setStatusFilter((s) => (s === 'warning' ? 'all' : 'warning'))
            }
            className={
              'px-4 py-2 rounded-md border transition text-sm ' +
              (statusFilter === 'warning'
                ? 'border-yellow-400 text-white bg-gray-700'
                : 'border-gray-600 text-gray-400')
            }
          >
            {warningMiners} Warning
          </button>
          <button
            onClick={() =>
              setStatusFilter((s) => (s === 'offline' ? 'all' : 'offline'))
            }
            className={
              'px-4 py-2 rounded-md border transition text-sm ' +
              (statusFilter === 'offline'
                ? 'border-red-400 text-white bg-gray-700'
                : 'border-gray-600 text-gray-400')
            }
          >
            {offlineMiners} Offline
          </button>
          <div className="px-4 py-2 rounded-md border border-gray-600 text-gray-400 ">
            Total Miners: {totalMiners}
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
      <div className="flex w-full justify-end ">
        <div className="flex items-end gap-3  p-3 ">
          {/* Search Input */}
          <div>
            <input
              type="text"
              value={searchInput}
              onChange={(e) => setSearchInput(e.target.value)}
              placeholder="Search by IP or name"
              aria-label="Search miners"
              className="px-3 py-2 text-sm border border-gray-600 bg-gray-800 rounded text-white placeholder-gray-400 w-64 focus:outline-none focus:ring-1 focus:ring-gray-500"
              onKeyDown={(e) => e.key === 'Enter' && handleSearch()}
            />

            {/* Clear Button */}
            <button
              onClick={clearSearch}
              className="px-3 py-2 text-sm text-gray-300 rounded border border-gray-600 bg-gray-900 hover:bg-gray-800 transition"
            >
              Clear
            </button>
          </div>
          {/* Sort Dropdown */}
          <div>
            <select
              value={sortBy}
              onChange={(e) =>
                setSortBy(
                  e.target.value as
                    | 'all'
                    | 'efficiency'
                    | 'hashrate'
                    | 'power'
                    | 'temperature'
                )
              }
              aria-label="Sort miners"
              className="px-3 py-2 text-sm border border-gray-600 bg-gray-800 rounded text-white focus:outline-none focus:ring-1 focus:ring-gray-500"
            >
              <option value="all">Sort</option>
              <option value="efficiency">Efficiency (W/TH)</option>
              <option value="hashrate">Hashrate (TH/s)</option>
              <option value="power">Power (W)</option>
              <option value="temperature">Temperature (°C)</option>
            </select>
          </div>
        </div>
        <div className="flex items-center gap-3">
          <div className="text-sm text-gray-400">
            {lastUpdate
              ? `Last update: ${lastUpdate.toLocaleString()}`
              : 'Never updated'}
          </div>
          <button
            onClick={refreshAllMiners}
            className="px-3 py-1 text-sm rounded border border-gray-600 text-white bg-gray-800 hover:bg-gray-700"
          >
            Refresh
          </button>
        </div>
      </div>

      {miners.length === 0 ? (
        <div className="text-center py-12 text-gray-400">
          <p className="text-lg">No miners found</p>
          <p className="text-sm mt-2">
            Add your miner by entering its IP address above
          </p>
        </div>
      ) : sortedDisplayedMiners.length === 0 ? (
        <div className="text-center py-12 text-gray-400">
          <p className="text-lg">No miners match your search</p>
        </div>
      ) : (
        <div className="flex overflow-x-auto space-x-4 pb-4">
          {sortedDisplayedMiners.map((miner) => (
            <DeviceCard key={miner.id} miner={miner} />
          ))}
        </div>
      )}
    </div>
  );
};

export default MinerInventoryDashboard;
