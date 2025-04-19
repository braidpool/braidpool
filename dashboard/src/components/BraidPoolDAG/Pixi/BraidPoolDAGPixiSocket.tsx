import React, { useEffect, useState, useRef, useCallback } from 'react';
import {
  GraphData,
  NodeIdMapping,
  ConnectionStatus,
} from './BraidPoolDAGTypes';
import {
  setupOptimizedSocket,
  getSocketUrl,
  getFallbackSocketUrl,
} from './BraidPoolDAGUtils';
import { Socket, io } from 'socket.io-client';
import './PixiSocket.css';
import { Button } from '@mui/material';

// Add this to prevent excessive reconnections
const RECONNECTION_COOLDOWN = 3000; // 3 seconds

interface BraidPoolDAGPixiSocketProps {
  onGraphDataLoaded: (data: GraphData, mapping: NodeIdMapping) => void;
  onConnectionStatusChange?: (status: ConnectionStatus) => void;
  debug?: boolean;
}

const BraidPoolDAGPixiSocket: React.FC<BraidPoolDAGPixiSocketProps> = ({
  onGraphDataLoaded,
  onConnectionStatusChange,
  debug = false,
}) => {
  const [connectionStatus, setConnectionStatus] = useState<ConnectionStatus>({
    connected: false,
    status: 'Connecting',
    message: 'Initializing connection...',
  });
  const [error, setError] = useState<string | null>(null);
  const socketRef = useRef<Socket | null>(null);
  const startTimeRef = useRef<number>(performance.now());
  const [elapsedTime, setElapsedTime] = useState<number>(0);

  const lastConnectionAttemptRef = useRef<number>(0);
  // Add a ref to know if component is mounted
  const isMountedRef = useRef<boolean>(true);

  // Show a hard timeout message after 15 seconds of waiting
  const [showTimeoutWarning, setShowTimeoutWarning] = useState<boolean>(false);

  // Track data loading metrics to show detailed progress
  const [loadingMetrics, setLoadingMetrics] = useState({
    connectTime: 0,
    processTime: 0,
    beadCount: 0,
    requestsSent: 0,
  });

  // Helper function to log with rate limiting
  const debugLog = useCallback(
    (message: string, force = false) => {
      if (debug || force) {
        console.log(message);
      }
    },
    [debug]
  );

  // Update elapsed time every 500ms for more responsive UI
  useEffect(() => {
    if (!connectionStatus.connected || connectionStatus.status === 'Active') {
      return;
    }

    const timer = setInterval(() => {
      const newElapsed = Math.round(
        (performance.now() - startTimeRef.current) / 1000
      );
      setElapsedTime(newElapsed);

      // Show timeout warning after 15 seconds
      if (newElapsed > 15 && !showTimeoutWarning) {
        setShowTimeoutWarning(true);
      }

      // Auto-reconnect after 30 seconds of no connection
      if (newElapsed > 30 && connectionStatus.status === 'Connecting') {
        debugLog(
          '⚠️ [PixiSocket] Connection timeout after 30s, auto-reconnecting',
          true
        );
        handleReconnect();
      }
    }, 500); // Update twice per second for smoother counting

    return () => clearInterval(timer);
  }, [connectionStatus, showTimeoutWarning, debugLog]);

  // Add a watchdog timer to detect when socket is connected but data doesn't arrive
  useEffect(() => {
    if (!connectionStatus.connected || connectionStatus.status === 'Active') {
      return;
    }

    // If we're connected but waiting for data too long (20+ seconds), try reconnecting
    if (connectionStatus.connected && connectionStatus.status === 'Connected') {
      const dataWatchdog = setTimeout(() => {
        if (!isMountedRef.current) return;

        if (connectionStatus.status !== 'Active') {
          debugLog(
            '⚠️ [PixiSocket] Connected but no data received for 20s, forcing reconnect',
            true
          );
          handleReconnect();
        }
      }, 20000);

      return () => clearTimeout(dataWatchdog);
    }
  }, [connectionStatus, debugLog]);

  // Track component mounting state
  useEffect(() => {
    isMountedRef.current = true;
    return () => {
      isMountedRef.current = false;
    };
  }, []);

  useEffect(() => {
    // Update parent with connection status if provided
    if (onConnectionStatusChange) {
      onConnectionStatusChange(connectionStatus);
    }

    // Track requests in the UI
    if (
      connectionStatus.message &&
      connectionStatus.message.includes('Requesting data')
    ) {
      setLoadingMetrics((prev) => ({
        ...prev,
        requestsSent: prev.requestsSent + 1,
      }));
    }
  }, [connectionStatus, onConnectionStatusChange]);

  // Main socket initialization effect - use useCallback to stabilize references
  const handleGraphData = useCallback(
    (data: GraphData) => {
      try {
        debugLog('📊 [PixiSocket] Processing graph data...');
        const processStartTime = performance.now();

        // Build the sequential ID mapping
        const newMapping: NodeIdMapping = {};
        let nextId = 1;
        Object.keys(data.parents).forEach((hash) => {
          if (!newMapping[hash]) {
            newMapping[hash] = nextId.toString();
            nextId++;
          }
        });

        // Update loading metrics
        setLoadingMetrics({
          connectTime: Math.round(processStartTime - startTimeRef.current),
          processTime: Math.round(performance.now() - processStartTime),
          beadCount: data.bead_count || 0,
          requestsSent: loadingMetrics.requestsSent,
        });

        // Send data to parent component
        onGraphDataLoaded(data, newMapping);

        debugLog(
          `✅ [PixiSocket] Data processed in ${Math.round(
            performance.now() - processStartTime
          )}ms`
        );
      } catch (err) {
        console.error('❌ [PixiSocket] Error processing graph data:', err);
        setError('Failed to process graph data. Please try again.');
      }
    },
    [onGraphDataLoaded, debug, debugLog]
  );

  const handleStatusChange = useCallback(
    (status: ConnectionStatus) => {
      debugLog(
        `🔌 [PixiSocket] Connection status: ${status.status} - ${status.message}`
      );
      setConnectionStatus(status);
    },
    [debugLog]
  );

  const handleError = useCallback(
    (message: string) => {
      console.error('⚠️ [PixiSocket] Connection error:', message);

      // Create a more helpful error message
      let errorMessage = message;

      // Check if this is a WebSocket-related error
      if (
        message.includes('WebSocket') ||
        message.includes('socket') ||
        message.includes('transport')
      ) {
        errorMessage = `WebSocket connection issue: ${message}. Try refreshing the page.`;
      }

      setError(errorMessage);

      // Immediately update connection status to prevent unnecessary rendering
      const errorStatus: ConnectionStatus = {
        connected: false,
        status: 'Error',
        message: errorMessage,
      };

      setConnectionStatus(errorStatus);

      // Notify parent about connection issue
      if (onConnectionStatusChange) {
        onConnectionStatusChange(errorStatus);
      }
    },
    [onConnectionStatusChange, debugLog]
  );

  useEffect(() => {
    debugLog('🔄 [PixiSocket] Initializing socket connection');

    // Prevent multiple initializations in a short time
    const now = Date.now();
    if (now - lastConnectionAttemptRef.current < RECONNECTION_COOLDOWN) {
      debugLog('⏱️ [PixiSocket] Skipping connection attempt - cooldown active');
      return;
    }
    lastConnectionAttemptRef.current = now;

    startTimeRef.current = performance.now();

    // Clear any previous errors and warning states
    setError(null);
    setShowTimeoutWarning(false);

    // Reset metrics
    setLoadingMetrics({
      connectTime: 0,
      processTime: 0,
      beadCount: 0,
      requestsSent: 0,
    });

    // Create the optimized socket connection with better error handling
    if (socketRef.current) {
      debugLog('🧹 [PixiSocket] Cleaning up existing socket connection');
      try {
        socketRef.current.disconnect();
      } catch (err) {
        console.warn('🧹 [PixiSocket] Error while disconnecting socket:', err);
      }
      socketRef.current = null;
    }

    // Implement multiple connection attempts
    debugLog('🔄 [PixiSocket] Starting primary connection attempt');

    // Try primary connection
    socketRef.current = setupOptimizedSocket(
      handleGraphData,
      handleStatusChange,
      handleError
    );

    // If primary fails after 8 seconds, try alternate URL directly
    setTimeout(() => {
      if (
        isMountedRef.current &&
        (!socketRef.current?.connected || connectionStatus.status !== 'Active')
      ) {
        debugLog(
          '🔀 [PixiSocket] Primary connection timed out, trying alternate connection method'
        );

        if (socketRef.current) {
          try {
            socketRef.current.disconnect();
          } catch (e) {
            console.warn('Error disconnecting timed out socket:', e);
          }
        }

        // Try with fallback URL and different parameters
        const fallbackUrl = getFallbackSocketUrl();
        debugLog(`🔄 [PixiSocket] Trying fallback URL: ${fallbackUrl}`);

        // Create a fresh socket with different parameters
        socketRef.current = io(fallbackUrl, {
          transports: ['polling', 'websocket'],
          forceNew: true,
          reconnection: true,
          reconnectionAttempts: 3,
          timeout: 5000,
        });

        // Set up all the handlers again
        socketRef.current.on('connect', () => {
          debugLog('✅ [PixiSocket] Fallback connection successful!');
          handleStatusChange({
            connected: true,
            status: 'Connected',
            message: 'Connected via fallback method. Requesting data...',
          });
          socketRef.current?.emit('get-graph-data');
        });

        socketRef.current.on('braid_update', (data) => {
          debugLog('📊 [PixiSocket] Received data via fallback!');
          handleGraphData(data);
        });

        socketRef.current.on('connect_error', (err: Error) =>
          handleError(`Connection failed: ${err.message}`)
        );
        socketRef.current.on('error', (err) =>
          handleError(`Socket error: ${err}`)
        );
      }
    }, 8000);

    // Cleanup on unmount
    return () => {
      debugLog('🧹 [PixiSocket] Cleaning up socket connection');
      if (socketRef.current) {
        try {
          socketRef.current.disconnect();
          socketRef.current = null;
        } catch (err) {
          console.warn('Error during socket cleanup:', err);
        }
      }
    };
  }, [debug, handleGraphData, handleStatusChange, handleError, debugLog]);

  // Update the connection retry method to match the working implementation
  const trySocketConnection = () => {
    const url = 'http://french.braidpool.net:65433/';
    debugLog(`🔄 [PixiSocket] Trying direct websocket connection`);

    // Show attempting status
    setConnectionStatus({
      connected: false,
      status: 'Retrying',
      message: 'Attempting to reconnect via websocket...',
    });

    // First disconnect any existing socket
    if (socketRef.current) {
      try {
        socketRef.current.disconnect();
      } catch (e) {
        console.error('Error disconnecting socket:', e);
      }
      socketRef.current = null;
    }

    // Create new socket with websocket transport ONLY
    socketRef.current = io(url, {
      transports: ['websocket'], // Force websocket only
      forceNew: true,
      reconnection: true,
      reconnectionAttempts: 5,
      reconnectionDelay: 1000,
      timeout: 20000,
      withCredentials: false, // Disable credentials
    });

    console.log('🔌 Attempting connection with WEBSOCKET transport only');

    // Rest of your event handlers...
  };

  // Update handleReconnect to use the new method
  const handleReconnect = () => {
    debugLog('🔄 [PixiSocket] Manual reconnect requested');

    // Prevent rapid reconnection attempts
    const now = Date.now();
    if (now - lastConnectionAttemptRef.current < RECONNECTION_COOLDOWN) {
      debugLog('⏱️ [PixiSocket] Reconnect ignored - cooldown active');
      return;
    }
    lastConnectionAttemptRef.current = now;

    // Reset state
    setError(null);
    setShowTimeoutWarning(false);
    setElapsedTime(0);
    startTimeRef.current = performance.now();

    // Reset metrics
    setLoadingMetrics({
      connectTime: 0,
      processTime: 0,
      beadCount: 0,
      requestsSent: 0,
    });

    // Try the new connection method
    trySocketConnection();
  };

  // Format elapsed time for display
  const formatTime = (seconds: number): string => {
    if (seconds < 60) return `${seconds}s`;
    const minutes = Math.floor(seconds / 60);
    const remainingSeconds = seconds % 60;
    return `${minutes}m ${remainingSeconds}s`;
  };

  // Diagnostic function with enhanced debugging
  const diagnoseConnection = () => {
    console.log('🔍 [DEBUG] Running connection diagnostics...');
    console.log('📊 Current Socket State:', {
      ref: socketRef.current ? 'exists' : 'null',
      connection: connectionStatus,
      error: error,
      elapsed: elapsedTime,
    });

    // Test both URLs directly using fetch
    const urls = [getSocketUrl(), getFallbackSocketUrl()];
    urls.forEach((url, index) => {
      console.log(`🌐 [DEBUG] Testing URL ${index + 1}: ${url}`);
      fetch(url, {
        method: 'GET',
        mode: 'cors',
        cache: 'no-store',
        headers: {
          Accept: 'text/html,application/xhtml+xml,application/xml',
        },
      })
        .then((response) => {
          console.log(
            `✅ HTTP request to ${url} successful: ${response.status}`
          );
          return response.text();
        })
        .then((text) => {
          console.log(
            `📄 Server response preview (${url}): ${text.substring(0, 100)}...`
          );
        })
        .catch((err) => {
          console.error(`❌ HTTP request to ${url} failed: ${err}`);
        });
    });

    // Check if we're behind a proxy or firewall
    const isLocalhost =
      window.location.hostname === 'localhost' ||
      window.location.hostname === '127.0.0.1';
    console.log(
      `🌐 Running on: ${window.location.hostname} (${
        isLocalhost ? 'localhost' : 'remote server'
      })`
    );

    // Try to establish a direct connection
    try {
      console.log('🔄 [DEBUG] Attempting to create a test socket directly');
      const testSocket = io(getSocketUrl(), {
        transports: ['websocket', 'polling'],
        timeout: 5000,
      });

      testSocket.on('connect', () => {
        console.log(
          '✅ [DEBUG] Test socket connected successfully!',
          testSocket.id
        );
        // Try to get data
        testSocket.emit('get-graph-data');

        // Clean up after 5 seconds
        setTimeout(() => {
          console.log('🧹 [DEBUG] Cleaning up test socket');
          testSocket.disconnect();
        }, 5000);
      });

      testSocket.on('connect_error', (err) => {
        console.error('❌ [DEBUG] Test socket connection error:', err);
      });

      testSocket.on('disconnect', (reason) => {
        console.log('🔌 [DEBUG] Test socket disconnected:', reason);
      });

      testSocket.on('braid_update', (data) => {
        console.log('📊 [DEBUG] Test socket received data!', Object.keys(data));
      });

      // Show current socket state of main socket
      if (socketRef.current) {
        console.log('🔌 Current main socket state:', {
          connected: socketRef.current.connected,
          id: socketRef.current.id || 'none',
          activeTransport:
            socketRef.current.io?.engine?.transport?.name || 'none',
          connected_state: socketRef.current.connected ? 'yes' : 'no',
          hasListeners: socketRef.current.hasListeners('connect'),
          reconnection: socketRef.current.io?.reconnection,
        });
      }
    } catch (err) {
      console.error('❌ [DEBUG] Error creating test socket:', err);
    }
  };

  // Render loading indicator with debug button for error situations
  return debug ? (
    <div
      className='pixi-socket-status'
      style={{
        display: 'block',
        position: 'fixed',
        bottom: '20px',
        right: '20px',
        zIndex: 1000,
        background: 'rgba(255,255,255,0.9)',
        padding: '15px',
        borderRadius: '8px',
        boxShadow: '0 0 10px rgba(0,0,0,0.2)',
      }}>
      <div>
        <h4>Socket Status: {connectionStatus.status}</h4>
        <p>{connectionStatus.message}</p>
        <p>Connection: {connectionStatus.connected ? 'Yes' : 'No'}</p>
        <p>Time Elapsed: {formatTime(elapsedTime)}</p>
        <Button
          variant='contained'
          color='primary'
          onClick={handleReconnect}
          sx={{ mr: 1, bgcolor: '#4caf50' }}>
          Try Direct WebSocket
        </Button>
        <Button
          variant='outlined'
          color='secondary'
          onClick={diagnoseConnection}>
          Diagnose
        </Button>
      </div>

      {error && (
        <div className='pixi-socket-error'>
          <h3>Connection Error</h3>
          <p>{error}</p>
          <Button
            variant='contained'
            color='primary'
            onClick={handleReconnect}
            sx={{ mr: 1 }}>
            Try Again
          </Button>
          {debug && (
            <Button
              variant='outlined'
              color='secondary'
              onClick={diagnoseConnection}>
              Diagnose Connection
            </Button>
          )}
        </div>
      )}
      {showTimeoutWarning && !error && (
        <div className='pixi-socket-loading'>
          <div className='pixi-socket-title'>
            Connection is taking longer than usual
          </div>
          <div className='pixi-socket-message'>
            We're still trying to connect to the server (
            {formatTime(elapsedTime)})
          </div>
          <Button variant='contained' onClick={handleReconnect}>
            Try Again
          </Button>
          {debug && (
            <Button
              variant='outlined'
              color='secondary'
              onClick={diagnoseConnection}
              sx={{ mt: 1 }}>
              Diagnose Connection
            </Button>
          )}
        </div>
      )}
    </div>
  ) : null; // Return null when not in debug mode
};

export default BraidPoolDAGPixiSocket;
