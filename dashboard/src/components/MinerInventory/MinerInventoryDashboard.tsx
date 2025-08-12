import { useState } from 'react';

import { Miner } from './Types';


const DeviceCard = ({ miner }: { miner: Miner }) => {
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

  const statusColor = getStatusColor(miner.status);

  return (
    <div className="relative w-full max-w-[400px] border border-gray-700 rounded-xl p-5 backdrop-blur-sm transition-transform duration-200 hover:-translate-y-1 hover:shadow-xl">
      <div className={`absolute top-3 right-3 w-3 h-3 rounded-full ${statusColor}`} />
      
      {miner.alerts > 0 && (
        <div className="absolute top-2 right-10 px-2 py-0.5 text-xs rounded-full bg-red-100 dark:bg-red-900 text-red-700 dark:text-red-300">
          ⚠ {miner.alerts}
        </div>
      )}

      <div className="flex items-center justify-between mb-3">
        <h3 className="text-lg font-semibold text-white">{miner.name}</h3>
        {miner.ismining && <span className="text-xs bg-green-600 text-white px-2 py-1 rounded">MINING</span>}
      </div>

      <div className="flex justify-between text-xs text-gray-400 mb-3">
        <span>MAC: {miner.mac}</span>
        <span>Last Seen: {miner.lastSeen}</span>
      </div>

      <div className="text-sm text-gray-300 space-y-2 mb-4">
        <div className="flex justify-between">
          <span>Hashrate: <span className="text-green-400">{miner.hashrate} TH/s</span></span>
          <span>Efficiency: {miner.efficiency} W/TH</span>
        </div>
        
        <div className="flex justify-between">
          <span>Model: {miner.ASICModel}</span>
          <span>Firmware: {miner.firmware}</span>
        </div>
        
        <div className="flex justify-between">
          <span>Power: <span className="text-blue-400">{miner.powerDraw} W</span></span>
          <span>Uptime: {miner.uptime}</span>
        </div>
        
        <div className="flex justify-between">
          <span>Avg Temp: <span className={miner.temp > 80 ? 'text-red-400' : miner.temp > 70 ? 'text-yellow-400' : 'text-green-400'}>{miner.temp}°C</span></span>
          <span>Chip Temp: <span className={miner.chipTemp > 75 ? 'text-red-400' : miner.chipTemp > 65 ? 'text-yellow-400' : 'text-green-400'}>{miner.chipTemp}°C</span></span>
        </div>
        
        <div className="flex justify-between">
          <span>Fan Speed: {miner.fanspeed} RPM</span>
          <span>Voltage: {miner.voltage} mV</span>
        </div>
        
        <div className="flex justify-between">
          <span>Pool: {miner.pools}</span>
          <span>IP: {miner.location.replace('IP: ', '')}</span>
        </div>
      </div>

      <div className="flex justify-between items-center mt-3 pt-3 border-t border-gray-700">
        <div className="text-xs text-gray-400">
          Expected: 99% hashrate
        </div>
        <button className="text-xs px-3 py-1 rounded border border-gray-600 text-white hover:bg-gray-700 transition flex items-center gap-1">
          Details
        </button>
      </div>
    </div>
  );
};

const MinerInventoryDashboard = () => {
  const [miners, setMiners] = useState<Miner[]>([]);
  const [loading, setLoading] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [newMinerIP, setNewMinerIP] = useState('');

  const API_BASE_URL = 'http://localhost:5001';

  // Helper functions
  const determineStatus = (data: any): 'online' | 'warning' | 'offline' => {
    if (!data.is_mining || !data.hashrate?.rate) return 'offline';
    if (data.temperature_avg > 85 || data.errors?.length > 0) return 'warning';
    return 'online';
  };

  const formatUptime = (seconds: number): string => {
    const days = Math.floor(seconds / 86400);
    const hours = Math.floor((seconds % 86400) / 3600);
    const minutes = Math.floor((seconds % 3600) / 60);
    
    if (days > 0) return `${days}d ${hours}h`;
    if (hours > 0) return `${hours}h ${minutes}m`;
    return `${minutes}m`;
  };

  const countAlerts = (data: any): number => {
    let alerts = 0;
    if (data.temperature_avg > 85) alerts++;
    if (data.hashboards?.[0]?.chip_temp > 80) alerts++;
    if (!data.is_mining) alerts++;
    if (data.errors && data.errors.length > 0) alerts += data.errors.length;
    return alerts;
  };

  const extractPoolName = (data: any): string => {
    try {
      const poolUrl = data.config?.pools?.groups?.[0]?.pools?.[0]?.url;
      if (poolUrl) {
        const match = poolUrl.match(/\/\/(.*?):/);
        return match ? match[1] : 'Unknown Pool';
      }
      return 'No Pool';
    } catch {
      return 'Unknown';
    }
  };

  const addMinerByIP = async () => {
    if (!newMinerIP.trim()) {
      alert('Please enter a valid IP address');
      return;
    }

    setLoading(true);
    setError(null);

    try {
      const response = await fetch(
        `${API_BASE_URL}/api/miners?ip=${newMinerIP.trim()}`,
        {
          headers: { Accept: 'application/json' },
        }
      );

      const responseData = await response.json();
      
      if (!response.ok) {
        throw new Error(responseData.error || `Failed to fetch from ${newMinerIP}`);
      }
      const data = responseData.raw_data || responseData;

      const newMiner: Miner = {
        id: data.mac || newMinerIP + '_' + Date.now(),
        name: data.hostname || 'BitAxe',
        status: determineStatus(data),
        temp: Math.round(data.temperature_avg || 0),
        hashrate: (data.hashrate?.rate || 0).toFixed(3),
        efficiency: (data.efficiency || 0).toString(),
        powerDraw: (data.wattage || 0).toString(),
        maxPower: data.wattage_limit?.toString() || 'No Limit',
        uptime: formatUptime(data.uptime || 0),
        location: `IP: ${newMinerIP}`,
        lastSeen: new Date().toLocaleTimeString(),
        alerts: countAlerts(data),
        frequency: 'N/A', 
        fanspeed: data.fans?.[0]?.speed?.toString() || '0',
        bestDiff: 'N/A',
        ASICModel: `${data.make} ${data.model}` || 'Unknown',
        chipTemp: Math.round(data.hashboards?.[0]?.chip_temp || 0),
        voltage: Math.round(data.hashboards?.[0]?.voltage || 0).toString(),
        firmware: `${data.firmware} ${data.fw_ver}` || 'Unknown',
        pools: extractPoolName(data),
        mac: data.mac || 'Unknown',
        ismining: data.is_mining || false
      };

      setMiners(prev => {
        const exists = prev.find(m => m.id === newMiner.id);
        if (exists) {
          return prev.map(m => m.id === newMiner.id ? newMiner : m);
        }
        return [...prev, newMiner];
      });

      setNewMinerIP('');

    } catch (err) {
      const errorMsg = err instanceof Error ? err.message : 'Unknown error occurred';
      setError(errorMsg);
      alert(`Could not connect to miner: ${errorMsg}`);
    } finally {
      setLoading(false);
    }
  };

  const clearMiners = () => {
    setMiners([]);
    setError(null);
  };

  const totalMiners = miners.length;
  const onlineMiners = miners.filter(m => m.status === 'online').length;
  const warningMiners = miners.filter(m => m.status === 'warning').length;
  const offlineMiners = miners.filter(m => m.status === 'offline').length;
  const totalHashrate = miners.reduce((sum, m) => sum + parseFloat(m.hashrate), 0);
  const totalPower = miners.reduce((sum, m) => sum + parseFloat(m.powerDraw), 0);

  return (
    <div className="min-h-screen text-white p-6">
      <div className="text-center mb-8">
        <h1 className="text-3xl font-bold text-white mb-2"> Mining Dashboard</h1>
        

        {error && (
          <div className="text-red-400 border border-red-600 px-4 py-3 rounded mt-4 max-w-md mx-auto">
            <strong className="font-bold">Error: </strong>
            <span className="block sm:inline">{error}</span>
          </div>
        )}

        <div className="flex justify-center items-center gap-2 mt-4">
          <input
            type="text"
            value={newMinerIP}
            onChange={(e) => setNewMinerIP(e.target.value)}
            placeholder="Enter BitAxe IP (e.g. 192.168.1.100)"
            className="px-3 py-2 text-sm bg-gray-800 border border-gray-600 rounded text-white placeholder-gray-400 w-64"
            onKeyPress={(e) => e.key === 'Enter' && addMinerByIP()}
          />
          <button
            onClick={addMinerByIP}
            disabled={loading}
            className="px-4 py-2 text-sm bg-gray-800 disabled:bg-gray-600 text-white rounded transition-colors"
          >
            {loading ? 'Adding...' : 'Add '}
          </button>
          <button
            onClick={clearMiners}
            className="px-4 py-2 text-sm bg-gray-800 text-white rounded transition-colors"
          >
            Clear All
          </button>
        </div>

        {/* Summary Stats */}
        <div className="flex flex-wrap justify-center gap-3 mt-6 text-sm">
          <div className="px-4 py-2 rounded-md border border-gray-600 text-green-400 bg-green-900/20">
            {onlineMiners} Online
          </div>
          <div className="px-4 py-2 rounded-md border border-gray-600 text-yellow-400 bg-yellow-900/20">
            {warningMiners} Warning
          </div>
          <div className="px-4 py-2 rounded-md border border-gray-600 text-red-400 bg-red-900/20">
            {offlineMiners} Offline
          </div>
          <div className="px-4 py-2 rounded-md border border-gray-600 text-blue-400 bg-blue-900/20">
            {totalMiners} Total
          </div>
          <div className="px-4 py-2 rounded-md border border-gray-600 text-purple-400 bg-purple-900/20">
            {totalHashrate.toFixed(3)} TH/s Total
          </div>
          <div className="px-4 py-2 rounded-md border border-gray-600 text-orange-400 bg-orange-900/20">
            {totalPower}W Total
          </div>
        </div>
      </div>

      {miners.length === 0 ? (
        <div className="text-center py-12 text-gray-400">
          
          <p className="text-lg">No  miners found</p>
          <p className="text-sm mt-2">Add your miner by entering its IP address above</p>
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