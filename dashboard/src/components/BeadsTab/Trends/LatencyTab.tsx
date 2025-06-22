import React, { useState, useCallback } from 'react';
import AdvancedChart from '../AdvancedChart';
import AnimatedStatCard from '../AnimatedStatCard';
import { LatencyTabProps } from '../lib/types';
import { useWebSocket } from '../Hooks/useWebSocket';
import { LatencyDataPoint } from '../lib/types';


export default function LatencyTab({
  chartHovered,
  setChartHovered,
  timeRange,
}: Omit<LatencyTabProps, 'isChartLoading' | 'chartData'>) {
  const [chartData, setChartData] = useState<LatencyDataPoint[]>([]);
  const [isLoading, setIsLoading] = useState(true);
  const [averageLatency, setAverageLatency] = useState('0ms');
  const [peakLatency, setPeakLatency] = useState('0ms');
  const [totalPeers, setTotalPeers] = useState(0);
  const [validPings, setValidPings] = useState(0);

  const handleMessage = useCallback((message: any) => {
    if (message.type === 'latency_update') {
      const data = message.data;
      
      setAverageLatency(data.averageLatency || '0ms');
      setPeakLatency(data.peakLatency || '0ms');
      setTotalPeers(data.totalPeers || data.peerCount || 0);
      setValidPings(data.validPings || 0);
      
      const formattedData: LatencyDataPoint[] = (data.chartData || []).map((d: any) => {
        let parsedDate: Date;
        try {
          parsedDate = new Date(d.date || d.timeStamp);
          if (isNaN(parsedDate.getTime())) {
            parsedDate = new Date(); 
          }
        } catch {
          parsedDate = new Date(); 
        }
        
        return {
          value: d.value,
          date: parsedDate,
          label: d.label || parsedDate.toLocaleTimeString('en-US', { 
            hour: '2-digit', 
            minute: '2-digit', 
            second: '2-digit',
            hour12: true 
          }),
        };
      });
      
      setChartData(formattedData);
      if(formattedData.length > 0) {
        setIsLoading(false);
      }
    }
  }, []);

  const handleError = useCallback((error: any) => {
    console.error('[LatencyTab] WebSocket error:', error);
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
          <h3 className="text-xl font-bold text-blue-300">Network Latency</h3>
          <p className="text-sm text-gray-400 mt-1">
            Real-time latency measurements from peer nodes
          </p>
        </div>
        <div className="bg-purple-900/30 px-3 py-1 rounded-md">
          <span className="text-purple-300 font-mono">
            Avg: {averageLatency} | {validPings}/{totalPeers} peers
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
          primaryLabel="Latency (ms)"
          tooltipFormatter={(value, name) => [`${value} ms`, name]}
        />
      </div>

      <div className="grid grid-cols-3 md:grid-cols-3 gap-6">
        <AnimatedStatCard
          title="Average Latency"
          value={averageLatency}       
        />
        <AnimatedStatCard
          title="Peak Latency"
          value={peakLatency}         
        />
        <AnimatedStatCard
          title="Active Peers"
          value={`${validPings}/${totalPeers}`}       
        />
      </div>
    </div>
  );
}
