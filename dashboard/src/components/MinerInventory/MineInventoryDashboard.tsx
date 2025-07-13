import { useState, useEffect } from 'react';
import Card from '../common/Card';
import { Miner, MinerStatus } from './Type';

const DeviceCard = ({
  miner,
  onActivateLight,
}: {
  miner: Miner;
  onActivateLight: (id: string) => void;
}) => {
  const getStatusColor = (status: MinerStatus) => {
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
    <div className="relative w-full max-w-[360px] bg-[#1c1c1c] border border-gray-700 rounded-xl p-5 backdrop-blur-sm transition-transform duration-200 hover:-translate-y-1 hover:shadow-xl">
 
  <div className={`absolute top-3 right-3 w-3 h-3 rounded-full ${statusColor}`} />
  {miner.alerts > 0 && (
    <div className="absolute top-2 right-10 px-2 py-0.5 text-xs rounded-full bg-red-100 dark:bg-red-900 text-red-700 dark:text-red-300">
      ⚠ {miner.alerts}
    </div>
  )}

  {/* Header */}
  <h3 className="text-lg font-semibold text-white mb-1">{miner.name}</h3>
  <div className="flex justify-between text-xs text-gray-400 mb-3">
    <span>{miner.location}</span>
    <span>{miner.lastSeen}</span>
  </div>

  {/* Stats Block  */}
  
<div className="text-sm text-gray-300 space-y-2 mb-4">
  <div className="flex justify-between">
    <span>Hashrate: {miner.hashrate} TH/s</span>
    <span>Temp: {miner.temp}°C</span>
  </div>
  <div className="flex justify-between">
    <span>Power: {miner.powerDraw} W</span>
    <span>Uptime: {miner.uptime}</span>
  </div>
  <div>
    <span>Efficiency: {miner.efficiency}</span>
  </div>
</div>



  {/* Action Buttons */}
  <div className="flex justify-between mt-2">
    <button
      className="text-xs px-3 py-1 rounded border border-blue-500 text-blue-500 hover:bg-blue-600 hover:text-white transition"
      onClick={() => console.log(`📊 Details for ${miner.id}`)}
    >
      Details
    </button>
    <button
      className="text-xs px-3 py-1 rounded border border-blue-500 text-blue-500 hover:bg-blue-600 hover:text-white transition flex items-center gap-1"
      onClick={() => onActivateLight(miner.id)}
    >
      💡 Locate
    </button>
  </div>
</div>

  );
};

const MineInventoryDashboard = () => {
  const [miners, setMiners] = useState<Miner[]>([]);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const [activeLight, setActiveLight] = useState<string | null>(null);
  const [newMinerIP, setNewMinerIP] = useState('');
useEffect(() => {
  const fetchMiners = async () => {
    try {
      const response = await fetch('http://localhost:5000/api/miners', {
        headers: { Accept: 'application/json' },
      });

      if (!response.ok) throw new Error('Failed to fetch miner data');

      const data = await response.json();

      const updatedMiner: Miner = {
        id: data.macAddr || 'default',
        name: data.hostname || 'Unknown',
        status: data.hashRate > 0 ? 'online' : data.overheat_mode ? 'warning' : 'offline',
        temp: data.temp || 0,
        hashrate: (data.hashRate || 0).toFixed(2),
        efficiency: ((data.hashRate / data.power) || 0).toFixed(2),
        powerDraw: (data.power || 0).toFixed(2),
        uptime: `${Math.floor((data.uptimeSeconds || 0) / 60)} min`,
        location: 'Local Network',
        lastSeen: new Date().toLocaleTimeString(),
        alerts: data.overheat_mode ? 1 : 0,
      };

      // Update only the matching miner or add if not present
      setMiners((prev) => {
        const index = prev.findIndex((m) => m.id === updatedMiner.id);
        if (index !== -1) {
          const updated = [...prev];
          updated[index] = updatedMiner;
          return updated;
        }
        return [...prev, updatedMiner];
      });

    } catch (err) {
      setError(err instanceof Error ? err.message : 'Unknown error occurred');
    } finally {
      setLoading(false);
    }
  };

  fetchMiners();
  const interval = setInterval(fetchMiners, 30000);
  return () => clearInterval(interval);
}, []);


  const handleActivateLight = (id: string) => {
    setActiveLight(id);
    console.log(`Activating locate light for miner ${id}`);
    setTimeout(() => setActiveLight(null), 5000);
  };

  const addMinerByIP = async () => {
    if (!newMinerIP) return;

    try {
     const response = await fetch(`http://localhost:5000/api/miners?ip=${newMinerIP}`, {
        headers: { Accept: 'application/json' },
      });

      if (!response.ok) throw new Error('Failed to fetch from custom IP');

      const data = await response.json();

      const newMiner: Miner = {
        id: data.macAddr || newMinerIP,
        name: data.hostname || 'Unknown',
        status: data.hashRate > 0 ? 'online' : data.overheat_mode ? 'warning' : 'offline',
        temp: data.temp || 0,
        hashrate: (data.hashRate || 0).toFixed(2),
        efficiency: ((data.hashRate / data.power) || 0).toFixed(2),
        powerDraw: (data.power || 0).toFixed(2),
        uptime: `${Math.floor((data.uptimeSeconds || 0) / 60)} min`,
        location: `IP: ${newMinerIP}`,
        lastSeen: new Date().toLocaleTimeString(),
        alerts: data.overheat_mode ? 1 : 0,
      };

      setMiners((prev) => [...prev, newMiner]);
      setNewMinerIP('');
    } catch (err) {
      alert('Could not connect to the miner at that IP');
      console.error(err);
    }
  };

  const totalMiners = miners.length;
  const onlineMiners = miners.filter((m) => m.status === 'online').length;
  const warningMiners = miners.filter((m) => m.status === 'warning').length;
  const offlineMiners = miners.filter((m) => m.status === 'offline').length;

  if (loading) {
    return (
      <Card title="Mine Inventory" subtitle="Loading miner data...">
        <div className="flex justify-center py-8">
          <div className="animate-spin rounded-full h-8 w-8 border-b-2 border-blue-500"></div>
        </div>
      </Card>
    );
  }

  if (error) {
    return (
      <Card title="Mine Inventory" subtitle="Error loading data">
        <div className="text-red-700 px-4 py-3 rounded relative" role="alert">
          <strong className="font-bold">Error: </strong>
          <span className="block sm:inline">{error}</span>
        </div>
      </Card>
    );
  }

  return (
    <Card>
      <div className="text-center mb-8">
        
        <p className="text-base text-gray-400 mt-1">Status of all mining devices</p>

        {/* Add Miner Input */}
        <div className="flex justify-center items-center gap-2 mt-4">
          <input
            type="text"
            value={newMinerIP}
            onChange={(e) => setNewMinerIP(e.target.value)}
            placeholder="Enter miner IP (e.g. 192.168.29.105)"
            className="px-3 py-1 text-sm bg-gray-800 border border-gray-600 rounded text-white placeholder-gray-400 w-64"
          />
          <button
            onClick={addMinerByIP}
            className="px-3 py-1 text-sm bg-blue-600 hover:bg-blue-700 text-white rounded"
          >
            Add Miner
          </button>
        </div>

        {/* Status pills */}
        <div className="flex flex-wrap justify-center gap-3 mt-6 text-sm">
          <div className="px-4 py-1 rounded-full border border-green-500 text-green-500">{onlineMiners} Online</div>
          <div className="px-4 py-1 rounded-full border border-yellow-500 text-yellow-500">{warningMiners} Warning</div>
          <div className="px-4 py-1 rounded-full border border-red-500 text-red-500">{offlineMiners} Offline</div>
          <div className="px-4 py-1 rounded-full border border-blue-500 text-blue-500">{totalMiners} Total</div>
        </div>
      </div>

      {/* Device Grid */}
      {miners.length === 0 ? (
        <div className="text-center py-8 text-gray-500">
          No mining devices found. Please check your Bitaxe setup.
        </div>
      ) : (
       <div className="flex overflow-x-auto space-x-4 pb-4 ml-6">
  {miners.map((miner) => (
    <DeviceCard key={miner.id} miner={miner} onActivateLight={handleActivateLight} />
  ))}
</div>

      )}
    </Card>
  );
};

export default MineInventoryDashboard;
