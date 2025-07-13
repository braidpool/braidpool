import { useState, useEffect } from 'react';
import Card from '../common/Card';
import { Miner,MinerStatus } from './Type';

const DeviceCard = ({
  miner,
  onActivateLight,
}: {
  miner: Miner;
  onActivateLight: (id: string) => void;
}) => {
  const getStatusColor = (status: MinerStatus) => {
    switch (status) {
      case 'online': return 'bg-green-500';
      case 'warning': return 'bg-yellow-500';
      case 'offline': return 'bg-red-500';
      default: return 'bg-gray-500';
    }
  };

  const statusColor = getStatusColor(miner.status);
  return (
    <div className=" relative transition-all duration-200 hover:-translate-y-1 hover:shadow-lg border bg-[#1c1c1c]  border-gray-700 rounded-lg p-4 backdrop-blur-sm ml-4 ">
      <div className={`absolute top-3 right-3 w-3 h-3 rounded-full ${statusColor}`} />
      {miner.alerts > 0 && (
        <div className="absolute top-2 right-12 flex items-center gap-1 px-2 py-0.5 rounded-full text-xs bg-red-100 dark:bg-red-900 text-red-600 dark:text-red-300">
          ⚠ {miner.alerts}
        </div>
      )}

      <h3 className="text-lg font-medium mb-2 text-gray-900 dark:text-white">{miner.name}</h3>

      <div className="mb-4 flex justify-between text-xs text-gray-500 dark:text-gray-400">
  <p>{miner.location}</p>
  <p>Last seen: {miner.lastSeen}</p>
</div> 

      <div className="grid grid-cols-2 gap-2 mb-4 text-sm">
        <div>Hashrate: {miner.hashrate} TH/s</div>
        <div>Temp: {miner.temp}°C</div>
        <div>Power: {miner.powerDraw} W</div>
        <div>Uptime: {miner.uptime}</div>
        <div>Effeciency : {miner.efficiency}</div>
      </div>

      <div className="flex justify-between">
        <button
          className="text-xs px-3 py-1 rounded border border-blue-500 text-blue-500 hover:bg-blue-500 hover:bg-opacity-20 transition-colors"
          onClick={() => console.log(`📊 Details for ${miner.id}`)}
        >
          Details
        </button>
        <button
          className="text-xs px-3 py-1 rounded border border-blue-500 text-blue-500 hover:bg-blue-500 hover:bg-opacity-20 transition-colors flex items-center gap-1"
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

  useEffect(() => {
    const fetchMiners = async () => {
      try {
        const response = await fetch('http://localhost:5000/api/miners',
 {
          headers: {
            Accept: 'application/json',
          },
        });

        if (!response.ok) {
          throw new Error('Failed to fetch miner data');
        }

        const data = await response.json();

        const miner: Miner = {
          id: data.macAddr || 'Unknown',
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

        setMiners([miner]);
      } catch (err) {
        setError(err instanceof Error ? err.message : 'Unknown error occurred');
        setMiners([]);
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
        <div className=" text-red-700 px-4 py-3 rounded relative" role="alert">
          <strong className="font-bold">Error: </strong>
          <span className="block sm:inline">{error}</span>
        </div>
      </Card>
    );
  }

  return (
    <Card>
  <div className="text-center mb-6">
  <h2 className="text-xl font-semibold text-white">Mine Inventory</h2>
  <p className="text-sm text-gray-400">Status of all mining devices</p>

  <div className="flex flex-wrap justify-center gap-2 mt-4 text-sm">
    <div className="px-3 py-1 rounded-lg border border-green-500 text-green-500">{onlineMiners} Online</div>
    <div className="px-3 py-1 rounded-lg border border-yellow-500 text-yellow-500">{warningMiners} Warning</div>
    <div className="px-3 py-1 rounded-lg border border-red-500 text-red-500">{offlineMiners} Offline</div>
    <div className="px-3 py-1 rounded-lg border border-blue-500 text-blue-500">{totalMiners} Total</div>
  </div>
</div>

      {miners.length === 0 ? (
        <div className="text-center py-8 text-gray-500">
          No mining devices found. Please check your Bitaxe setup.
        </div>
      ) : (
        <div className="grid sm:grid-cols-1 md:grid-cols-2 lg:grid-cols-3 xl:grid-cols-4 gap-4">
          {miners.map((miner) => (
            <DeviceCard key={miner.id} miner={miner} onActivateLight={handleActivateLight} />
          ))}
        </div>
      )}
    </Card>
  );
};

export default MineInventoryDashboard;
