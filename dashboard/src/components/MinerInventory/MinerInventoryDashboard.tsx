import { useState, useEffect, useRef } from 'react';
import {
  Miner,
  HistoryPoint,
  MinerAnalyticsPoint,
  MinerAlert as Alert,
} from './Types';
import { API_URLS } from '../../URLs';
import AnalyticsCharts from './AnalyticsCharts';
import MinerTable from './MinerTable';
import MinerDashboardHeader from './MinerDashboardHeader';
import MinerControls from './MinerControls';
import { HISTORY_POINTS, THRESHOLDS, REFRESH_INTERVAL } from './Constant';

const MAX_HISTORY_POINTS = HISTORY_POINTS;

const MinerInventoryDashboard = () => {
  const [miners, setMiners] = useState<Miner[]>([]);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [newMinerIP, setNewMinerIP] = useState('');
  const [searchInput, setSearchInput] = useState('');
  const [searchQuery, setSearchQuery] = useState('');
  const [sortBy, setSortBy] = useState<
    'all' | 'efficiency' | 'hashrate' | 'power' | 'temperature'
  >('all');
  const [statusFilter, setStatusFilter] = useState<
    'all' | 'online' | 'warning' | 'offline'
  >('all');

  const [lastUpdate, setLastUpdate] = useState<Date | null>(null);
  const minersRef = useRef<Miner[]>([]);
  const [fleetHistory, setFleetHistory] = useState<HistoryPoint[]>([]);
  const [minerHistory, setMinerHistory] = useState<
    Record<string, MinerAnalyticsPoint[]>
  >({});
  const [expandedAlerts, setExpandedAlerts] = useState<Record<string, boolean>>(
    {}
  );

  const determineStatus = (data: any): 'online' | 'warning' | 'offline' => {
    if (data.is_online === false) return 'offline';
    if (!data.is_mining || (data.hashrate_current || 0) === 0) return 'offline';
    if (
      (data.temperature || 0) > THRESHOLDS.ASIC_TEMP_CRITICAL ||
      (data.vr_temperature || 0) > THRESHOLDS.VR_TEMP_CRITICAL ||
      data.errors?.length > 0
    )
      return 'warning';
    return 'online';
  };

  const mapApiToMiner = (m: any, lastSeenFallback = 'Never'): Miner => ({
    id: m.id,
    ip: m.ip,
    hostname: m.hostname || 'Unknown',
    mac: m.mac || 'Unknown',
    make: m.make || 'Unknown',
    model: m.model || 'Unknown',
    firmware: m.firmware || 'Unknown',
    status: determineStatus(m),
    is_mining: m.is_mining || false,
    uptime: m.uptime || 0,
    errors: m.errors || [],
    alerts: 0,
    lastSeen: m.last_seen
      ? new Date(m.last_seen).toLocaleTimeString()
      : lastSeenFallback,
    hashrate_current: m.hashrate_current || 0,
    hashrate_avg: m.hashrate_avg || 0,
    expected_hashrate: m.expected_hashrate || 0,
    temperature: m.temperature || 0,
    temperature_max: m.temperature_max || 0,
    vr_temperature: m.vr_temperature || 0,
    power_usage: m.power_usage || 0,
    power_limit: m.power_limit || 0,
    efficiency: m.efficiency || 0,
    voltage: m.voltage || 0,
    fan_speeds: m.fan_speeds || [],
    chip_count: m.chip_count || 0,
    primary_pool: m.primary_pool || 'No Pool',
    pools: m.pools || [],
  });

  useEffect(() => {
    const loadMinersFromDB = async () => {
      try {
        setLoading(true);
        const response = await fetch(`${API_URLS.MINER_DEVICE_URL}/api/miners`);
        const data = await response.json();
        if (data.success && data.miners) {
          setMiners(data.miners.map((m: any) => mapApiToMiner(m)));
          if (data.miners.length > 0) {
            setLastUpdate(new Date());
          }
        }
      } catch (err) {
        console.error('Failed to load miners from database:', err);
      } finally {
        setLoading(false);
      }
    };
    loadMinersFromDB();
  }, []);

  useEffect(() => {
    minersRef.current = miners;
  }, [miners]);

  useEffect(() => {
    if (miners.length === 0) return;
    const timestamp = Date.now();
    const totalHashrateNow = miners.reduce(
      (sum, m) =>
        m.status === 'online' || m.status === 'warning'
          ? sum + (m.hashrate_current || 0)
          : sum,
      0
    );
    const totalExpectedNow = miners.reduce(
      (sum, m) =>
        m.status === 'online' || m.status === 'warning'
          ? sum + (m.expected_hashrate || 0)
          : sum,
      0
    );
    const activeMiners = miners.filter(
      (m) => m.status === 'online' || m.status === 'warning'
    );

    const avgEfficiencyNow =
      activeMiners.length > 0
        ? activeMiners.reduce((sum, m) => sum + (m.efficiency || 0), 0) /
          activeMiners.length
        : 0;
    const avgTempNow =
      activeMiners.length > 0
        ? activeMiners.reduce((sum, m) => sum + (m.temperature || 0), 0) /
          activeMiners.length
        : 0;
    const avgVrTempNow =
      activeMiners.length > 0
        ? activeMiners.reduce((sum, m) => sum + (m.vr_temperature || 0), 0) /
          activeMiners.length
        : 0;

    setFleetHistory((prev) => {
      const next = [
        ...prev,
        {
          timestamp,
          totalHashrate: totalHashrateNow,
          expectedHashrate: totalExpectedNow,
          efficiency: avgEfficiencyNow,
          temperature: avgTempNow,
          vrTemperature: avgVrTempNow,
        },
      ];
      return next.slice(-MAX_HISTORY_POINTS);
    });

    setMinerHistory((prev) => {
      const next = { ...prev };
      miners.forEach((miner) => {
        const minerKey = miner.id;
        const history = next[minerKey] ?? [];
        const point: MinerAnalyticsPoint = {
          timestamp,
          hashrate: miner.hashrate_current || 0,
          expected: miner.expected_hashrate || 0,
          efficiency: (miner.efficiency || 0) * 1000,
          temperature: miner.temperature || 0,
          vrTemperature: miner.vr_temperature || 0,
        };
        next[minerKey] = [...history, point].slice(-MAX_HISTORY_POINTS);
      });
      return next;
    });
  }, [miners]);

  // Helper functions
  const getAlerts = (miner: Miner): Alert[] => {
    if (miner.status === 'offline') return [];
    const alerts: Alert[] = [];
    if (miner.temperature > THRESHOLDS.ASIC_TEMP_CRITICAL) {
      alerts.push({ message: `ASIC Temp High` });
    }
    if (miner.vr_temperature > THRESHOLDS.VR_TEMP_CRITICAL) {
      alerts.push({ message: `VR Temp High` });
    }
    if (miner.voltage && miner.voltage < THRESHOLDS.VOLTAGE_LOW) {
      alerts.push({ message: `Voltage Low` });
    }
    if (
      miner.fan_speeds !== undefined &&
      miner.fan_speeds.some((s) => s < THRESHOLDS.FAN_SPEED_LOW)
    ) {
      alerts.push({ message: `Fan Speed Low` });
    }
    return alerts;
  };

  const refreshAllMiners = async () => {
    const currentMiners = minersRef.current;
    if (currentMiners.length === 0) return;

    setLoading(true);

    try {
      const response = await fetch(
        `${API_URLS.MINER_DEVICE_URL}/api/miners/refresh/all`,
        {
          method: 'POST',
        }
      );

      const result = await response.json();

      if (result.miners) {
        const updatedMiners: Miner[] = result.miners.map((m: any) =>
          mapApiToMiner(m.miner || m, new Date().toLocaleTimeString())
        );
        setMiners(updatedMiners);
        setLastUpdate(new Date());
      }
    } catch (err) {
      console.error('Error refreshing miners:', err);
    }

    setLoading(false);
  };

  const refreshInterval = REFRESH_INTERVAL;
  useEffect(() => {
    if (miners.length === 0) return;

    const interval = setInterval(refreshAllMiners, refreshInterval * 1000);
    return () => clearInterval(interval);
  }, [refreshInterval, miners.length]);

  const addMinerByIP = async () => {
    if (!newMinerIP.trim()) {
      setError('Please enter a valid IP address');
      return;
    }

    setLoading(true);
    setError(null);

    try {
      const response = await fetch(`${API_URLS.MINER_DEVICE_URL}/api/miners`, {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ ip: newMinerIP.trim() }),
      });

      const result = await response.json();

      if (result.success && result.miner) {
        const newMiner = mapApiToMiner(result.miner, 'Now');

        setMiners((prev) => {
          const exists = prev.find((existing) => existing.ip === newMiner.ip);
          if (exists) {
            return prev.map((existing) =>
              existing.ip === newMiner.ip ? newMiner : existing
            );
          }
          return [...prev, newMiner];
        });
        setNewMinerIP('');
        setLastUpdate(new Date());

        if (result.warning) {
          setError(result.warning);
        }
      } else {
        setError(result.error || 'Failed to add miner');
      }
    } catch (err) {
      console.error('Error adding miner:', err);
      setError(`Could not connect to miner at ${newMinerIP.trim()}`);
    }

    setLoading(false);
  };

  const deleteMiner = async (minerId: string) => {
    try {
      const response = await fetch(
        `${API_URLS.MINER_DEVICE_URL}/api/miners/${minerId}`,
        {
          method: 'DELETE',
        }
      );

      const result = await response.json();
      if (result.success) {
        setMiners((prev) => prev.filter((m) => m.id !== minerId));
      } else {
        setError(result.error || 'Failed to delete miner');
      }
    } catch (err) {
      console.error('Error deleting miner:', err);
      setError('Failed to delete miner');
    }
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
    (sum, m) =>
      m.status === 'online' || m.status === 'warning'
        ? sum + (m.hashrate_current || 0)
        : sum,
    0
  );
  const totalPower = miners.reduce(
    (sum, m) =>
      m.status === 'online' || m.status === 'warning'
        ? sum + (m.power_usage || 0)
        : sum,
    0
  );
  const activeMiners = miners.filter(
    (m) => m.status === 'online' || m.status === 'warning'
  );

  const avgEfficiency =
    activeMiners.length > 0
      ? (activeMiners.reduce((sum, m) => sum + (m.efficiency || 0), 0) /
          activeMiners.length) *
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

  const statusStyles: Record<Miner['status'], string> = {
    online: 'bg-emerald-500/10 text-emerald-300 border-emerald-500/40',
    warning: 'bg-amber-500/10 text-amber-300 border-amber-500/40',
    offline: 'bg-rose-500/10 text-rose-300 border-rose-500/40',
  };

  return (
    <div className="min-h-screen w-full px-4 py-6 sm:px-6 lg:px-8">
      <div className="max-w-7xl mx-auto">
        <div className="text-center mb-8">
          <h1 className="text-3xl font-bold text-white mb-9">
            Mining Dashboard
          </h1>

          {error && (
            <div className="text-red-400 border border-red-500 px-4 py-3 rounded max-w-md mx-auto mb-4">
              <strong className="font-bold">Error: </strong>
              <span className="block sm:inline">{error}</span>
            </div>
          )}

          <MinerControls
            newMinerIP={newMinerIP}
            setNewMinerIP={setNewMinerIP}
            addMinerByIP={addMinerByIP}
            loading={loading}
            lastUpdate={lastUpdate}
          />

          <MinerDashboardHeader
            totalMiners={totalMiners}
            totalHashrate={totalHashrate}
            totalPower={totalPower}
            avgEfficiency={avgEfficiency}
          />
        </div>

        {miners.length > 0 && (
          <div className="mb-6">
            <AnalyticsCharts fleetHistory={fleetHistory} />
          </div>
        )}

        {miners.length === 0 ? (
          <div className="text-center py-12 text-gray-400">
            <p className="text-xl">No miners found</p>
            <p className="text-md mt-2">
              Add your miner by entering its IP address above
            </p>
          </div>
        ) : (
          <>
            <div className="flex flex-col gap-4 mb-6 sm:flex-row sm:items-center sm:justify-between">
              <div className="flex flex-wrap gap-2">
                <button
                  onClick={() =>
                    setStatusFilter((s) => (s === 'online' ? 'all' : 'online'))
                  }
                  className={
                    'px-4 py-2 rounded-md border transition text-sm  cursor-pointer ' +
                    (statusFilter === 'online'
                      ? 'border-blue-400 text-white bg-gray-700'
                      : 'border-gray-600 text-gray-400 hover:bg-gray-800')
                  }
                >
                  {onlineMiners} Online
                </button>
                <button
                  onClick={() =>
                    setStatusFilter((s) =>
                      s === 'warning' ? 'all' : 'warning'
                    )
                  }
                  className={
                    'px-4 py-2 rounded-md border transition text-sm  cursor-pointer ' +
                    (statusFilter === 'warning'
                      ? 'border-yellow-400 text-white bg-gray-700'
                      : 'border-gray-600 text-gray-400 hover:bg-gray-800')
                  }
                >
                  {warningMiners} Warning
                </button>
                <button
                  onClick={() =>
                    setStatusFilter((s) =>
                      s === 'offline' ? 'all' : 'offline'
                    )
                  }
                  className={
                    'px-4 py-2 rounded-md border transition text-sm   cursor-pointer ' +
                    (statusFilter === 'offline'
                      ? 'border-red-400 text-white bg-gray-700'
                      : 'border-gray-600 text-gray-400 hover:bg-gray-800')
                  }
                >
                  {offlineMiners} Offline
                </button>
              </div>

              <div className="flex flex-col sm:flex-row sm:items-center gap-2">
                <div className="flex gap-2">
                  <input
                    type="text"
                    value={searchInput}
                    onChange={(e) => setSearchInput(e.target.value)}
                    placeholder="Search by IP or name"
                    aria-label="Search miners"
                    className="px-3 py-2 text-sm border border-gray-600 bg-gray-800 rounded text-white placeholder-gray-400 focus:outline-none focus:ring-1 focus:ring-gray-500"
                    onKeyDown={(e) => e.key === 'Enter' && handleSearch()}
                  />
                  <button
                    onClick={clearSearch}
                    className="px-3 py-2 text-sm text-gray-300 rounded border border-gray-600 bg-gray-900 hover:bg-gray-800 transition whitespace-nowrap"
                  >
                    Clear
                  </button>
                </div>

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
                  <option value="all">Sort By</option>
                  <option value="efficiency">Efficiency (W/TH)</option>
                  <option value="hashrate">Hashrate (TH/s)</option>
                  <option value="power">Power (W)</option>
                  <option value="temperature">Temperature (°C)</option>
                </select>
              </div>
            </div>

            {/* Miners Table */}
            {sortedDisplayedMiners.length === 0 ? (
              <div className="text-center py-12 text-gray-400">
                <p className="text-lg">No miners match your search</p>
              </div>
            ) : (
              <MinerTable
                miners={sortedDisplayedMiners}
                minerHistory={minerHistory}
                getAlerts={getAlerts}
                expandedAlerts={expandedAlerts}
                setExpandedAlerts={setExpandedAlerts}
                statusStyles={statusStyles}
                onDelete={deleteMiner}
              />
            )}
          </>
        )}
      </div>
    </div>
  );
};

export default MinerInventoryDashboard;
