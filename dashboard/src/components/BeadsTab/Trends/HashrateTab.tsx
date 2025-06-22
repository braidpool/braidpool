import React, { useState, useCallback } from 'react';
import AdvancedChart from '../AdvancedChart';
import AnimatedStatCard from '../AnimatedStatCard';
import { useWebSocket } from '../Hooks/useWebSocket';

type HashrateDataPoint = {
  value: number;
  date: Date;
  label: string;
};

export default function HashrateTab({
  chartHovered,
  setChartHovered,
  timeRange,
}: {
  chartHovered: boolean;
  setChartHovered: (isHovered: boolean) => void;
  timeRange: string;
}) {
  const [chartData, setChartData] = useState<HashrateDataPoint[]>([]);
  const [isLoading, setIsLoading] = useState(true);
  const [currentHashrate, setCurrentHashrate] = useState('0 EH/s');
  const [peakHashrate, setPeakHashrate] = useState('0 EH/s');
  const [poolDominance, setPoolDominance] = useState('0%');
  const handleMessage = useCallback((message: any) => {
    if (message.type === 'hashrate_update') {
      const { history, current, peak, dominance } = message.data;

      const formattedData: HashrateDataPoint[] = (history || []).map((d: any) => ({
        value: parseFloat(d.value) || 0,
        date: new Date(d.date),
        label: new Date(d.date).toLocaleTimeString(),
      }));

      setChartData(formattedData);
      setCurrentHashrate(current || '0 EH/s');
      setPeakHashrate(peak || '0 EH/s');
      setPoolDominance(dominance || '0%');
      if (formattedData.length > 0) {
        setIsLoading(false);
      }
    }
  }, []);

  const handleError = useCallback((error: any) => {
    console.error('[HashrateTab] WebSocket error:', error);
    setIsLoading(false);
  }, []);

  const { isConnected } = useWebSocket({
    onMessage: handleMessage,
    onError: handleError
  });

  return (
    <div className="space-y-6 bg-[#1c1c1c]">
      <div className="flex justify-between items-center">
        <div>
          <h3 className="text-xl font-bold text-blue-300">Pool Hashrate</h3>
          <p className="text-sm text-gray-400 mt-1">
            Live hashrate of the Braidpool
          </p>
        </div>
        <div className="bg-emerald-900/30 px-3 py-1 rounded-md">
          <span className="text-emerald-300 font-mono">
            {currentHashrate}
          </span>
        </div>
      </div>

      <div
        className="relative border border-gray-800/50 rounded-xl p-6 h-auto bg-[#1c1c1c] backdrop-blur-md overflow-hidden"
        onMouseEnter={() => setChartHovered(true)}
        onMouseLeave={() => setChartHovered(false)}
      >
        <AdvancedChart
          data={chartData}
          height={350}
          isHovered={chartHovered}
          isLoading={isLoading || !isConnected}
          timeRange={timeRange}
          primaryLabel="Hashrate (EH/s)"
          tooltipFormatter={(value) => [`${value} EH/s`, 'Hashrate']}
        />
      </div>

      <div className="grid grid-cols-3 md:grid-cols-3 sm:grid-cols-1  gap-6">
        <AnimatedStatCard
          title="Current Hashrate"
          value={(currentHashrate)}
        />
        <AnimatedStatCard
          title="Peak Hashrate (24h)"
          value={(peakHashrate)}      
        />
        <AnimatedStatCard
          title="Pool Dominance"
          value={poolDominance}    
        />
      </div>
    </div>
  );
}
