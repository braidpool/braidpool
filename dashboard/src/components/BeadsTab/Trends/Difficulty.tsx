import { useEffect, useRef, useState } from 'react';
import ContextualError from '../../common/ContextualError';
import AdvancedChart from '../AdvancedChart';
import { WEBSOCKET_URLS } from '@/URLs';

export const Difficulty = () => {
  const [isConnected, setIsConnected] = useState(false);
  const [error, setError] = useState<string | null>(null);
  const [errorDetails, setErrorDetails] = useState<unknown>(null);
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
      setError(null);
      setErrorDetails(null);
    };

    ws.onerror = (error) => {
      console.error('[Difficulty] WebSocket error:', error);
      setIsConnected(false);
      setError('WebSocket connection error');
      setErrorDetails({
        component: 'Difficulty',
        endpoint: WEBSOCKET_URLS.MAIN_WEBSOCKET,
        eventType: error.type,
        readyState: ws.readyState,
      });
    };

    ws.onmessage = (event) => {
      if (!isMounted) return;
      try {
        const message = JSON.parse(event.data);
        if (message.type === 'error') {
          setError(
            typeof message.data === 'string'
              ? message.data
              : message.data?.message || 'Unknown error'
          );
          setErrorDetails({
            component: 'Difficulty',
            endpoint: WEBSOCKET_URLS.MAIN_WEBSOCKET,
            payload: message,
          });
          return;
        }
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
          setError(null);
          setErrorDetails(null);
        }
      } catch (e) {
        console.error('[Difficulty] Message parse error:', e);
        setError('Failed to parse data');
        setErrorDetails({
          component: 'Difficulty',
          endpoint: WEBSOCKET_URLS.MAIN_WEBSOCKET,
          error: e instanceof Error ? e.message : String(e),
          rawPayload: event.data,
        });
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
      {error && <ContextualError message={error} details={errorDetails} />}
      <div>
        <AdvancedChart
          data={chartData}
          yLabel="Difficulty"
          unit="T"
          lineColor="#8884d8"
          title="Network Difficulty"
          description="Bitcoin network difficulty over time (in Trillions)"
          headerRight={
            <div className="bg-purple-900/30 px-3 py-1 rounded-md">
              <span className="text-purple-300 font-mono">
                Current Difficulty :{' '}
                {chartData.length > 0
                  ? `${chartData[chartData.length - 1].value} T`
                  : error
                    ? 'No data'
                    : 'Loading...'}
              </span>
            </div>
          }
          downloadFileName="network-difficulty"
        />
      </div>
    </div>
  );
};
