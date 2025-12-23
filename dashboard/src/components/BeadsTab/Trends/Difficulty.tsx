import { useEffect, useRef, useState } from 'react';
import AdvancedChart from '../AdvancedChart';
import { WEBSOCKET_URLS } from '@/URLs';

export const Difficulty = () => {
  const [isConnected, setIsConnected] = useState(false);
  const wsRef = useRef<WebSocket | null>(null);
  const [chartData, setChartData] = useState<
    { value: number; timestamp: number }[]
  >([]);

  useEffect(() => {
    let isMounted = true;
    const ws = new WebSocket(WEBSOCKET_URLS.MAIN_WEBSOCKET);
    wsRef.current = ws;

    ws.onopen = () => {
      if (!isMounted) return;
      setIsConnected(true);
    };

    ws.onerror = (error) => {
      console.error('[Difficulty] WebSocket error:', error);
      setIsConnected(false);
    };

    ws.onmessage = (event) => {
      if (!isMounted) return;
      try {
        const message = JSON.parse(event.data);
        if (message.type === 'hashrate_data') {
          const { networkDifficulty, timestamp } = message.data;

          setChartData((prevData) => {
            const newPoint = {
              value: parseFloat(networkDifficulty.toFixed(2)), // Trillion unit
              timestamp: new Date(timestamp).getTime(),
            };

            const updated = [...prevData, newPoint];
            return updated.slice(-10);
          });
        }
      } catch (e) {
        console.error('[Difficulty] Message parse error:', e);
      }
    };

    ws.onclose = () => {
      if (!isMounted) return;
      console.log('[Difficulty] WebSocket closed');
      setIsConnected(false);
    };

    return () => {
      isMounted = false;
      ws.onopen = null;
      ws.onclose = null;
      ws.onerror = null;
      ws.onmessage = null;
      if (ws.readyState === WebSocket.OPEN) {
        ws.close();
      }
    };
  }, []);

  return (
    <div className="space-y-6 ">
      <div className="flex justify-between items-center">
        <div>
          <h3 className="text-xl font-bold text-blue-300">
            Network Difficulty
          </h3>
        </div>
        <div className="bg-purple-900/30 px-3 py-1 rounded-md">
          <span className="text-purple-300 font-mono">
            Current Difficulty :{' '}
            {chartData.length > 0
              ? `${chartData[chartData.length - 1].value} T`
              : 'Loading...'}
          </span>
        </div>
      </div>

      <div>
        <AdvancedChart
          data={chartData}
          yLabel="Difficulty"
          unit="T"
          lineColor="#8884d8"
        />
      </div>
    </div>
  );
};
