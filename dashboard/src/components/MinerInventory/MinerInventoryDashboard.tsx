import { useState, useEffect, useCallback, useRef } from 'react';
import { Miner, HistoryPoint } from './Types';
import { API_URLS, WEBSOCKET_URLS } from '../../URLs';
import AnalyticsCharts from './AnalyticsCharts';
import MinerTable from './MinerTable';
import MinerDashboardHeader from './MinerDashboardHeader';
import MinerControls from './MinerControls';
import { HISTORY_POINTS, REFRESH_INTERVAL } from './Constant';
import { mapApiToMiner, getAlerts } from './Utils';

const MAX_HISTORY_POINTS = HISTORY_POINTS;

const MinerInventoryDashboard = () => {
  const [miners, setMiners] = useState<Miner[]>([]);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [searchInput, setSearchInput] = useState('');
  const [searchQuery, setSearchQuery] = useState('');
  const [sortBy, setSortBy] = useState<
    'all' | 'efficiency' | 'hashrate' | 'power' | 'temperature'
  >('all');
  const [statusFilter, setStatusFilter] = useState<
    'all' | 'online' | 'warning' | 'offline'
  >('all');

  const [lastUpdate, setLastUpdate] = useState<Date | null>(null);
  const [wsConnected, setWsConnected] = useState(false);
  const wsRef = useRef<WebSocket | null>(null);
  const [fleetHistory, setFleetHistory] = useState<HistoryPoint[]>([]);
  useEffect(() => {
    let cancelled = false;
    const connect = () => {
      if (cancelled) return;
      const ws = new WebSocket(WEBSOCKET_URLS.MINER_DEVICE_WS);

      ws.onopen = () => {
        if (!cancelled) setWsConnected(true);
      };

      ws.onmessage = (event) => {
        if (cancelled) return;
        try {
          const data = JSON.parse(event.data as string);
          if (data.success && data.miners) {
            setMiners(data.miners.map((m: any) => mapApiToMiner(m)));
            setLastUpdate(new Date());
          }
        } catch (err) {
          console.warn('WS message parse error:', err);
        }
      };

      ws.onerror = () => {
        ws.close();
      };

      ws.onclose = () => {
        if (!cancelled) {
          setWsConnected(false);
          setTimeout(connect, 3000); // reconnect after 3 s
        }
      };

      wsRef.current = ws;
    };

    connect();
    return () => {
      cancelled = true;
      wsRef.current?.close();
    };
  }, []);

  const fetchMiners = useCallback(async () => {
    setLoading(true);
    setError(null);
    try {
      const response = await fetch(`${API_URLS.MINER_DEVICE_URL}/api/miners`);
      if (!response.ok)
        throw new Error(`HTTP ${response.status} ${response.statusText}`);
      const data = await response.json();
      if (data.success && data.miners) {
        setMiners(data.miners.map((m: any) => mapApiToMiner(m)));
        setLastUpdate(new Date());
      } else if (!data.success) {
        throw new Error(data.error || 'Failed to load miners');
      }
    } catch (err) {
      const message =
        err instanceof Error ? err.message : 'Failed to fetch miners';
      console.error('Failed to fetch miners:', err);
      setError(message);
    } finally {
      setLoading(false);
    }
  }, []);

  useEffect(() => {
    fetchMiners();
  }, [fetchMiners]);
  useEffect(() => {
    if (wsConnected) return;
    const interval = setInterval(fetchMiners, REFRESH_INTERVAL * 1000);
    return () => clearInterval(interval);
  }, [wsConnected, fetchMiners]);

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
  }, [miners]);

  const deleteMiner = async (minerId: string) => {
    try {
      const response = await fetch(
        `${API_URLS.MINER_DEVICE_URL}/api/miners/${minerId}`,
        {
          method: 'DELETE',
        }
      );

      const result = await response.json();
      if (!response.ok) {
        const errorMsg =
          result.detail?.error || result.detail || 'Failed to delete miner';
        setError(
          typeof errorMsg === 'string' ? errorMsg : JSON.stringify(errorMsg)
        );
        return;
      }

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
      ? activeMiners.reduce((sum, m) => sum + (m.efficiency || 0), 0) /
        activeMiners.length
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
            loading={loading}
            lastUpdate={lastUpdate}
            wsConnected={wsConnected}
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
              The backend is scanning your LAN automatically, miners will appear
              here once discovered.
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
                getAlerts={getAlerts}
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
