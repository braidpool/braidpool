import React, {
  useRef,
  useEffect,
  useState,
  useMemo,
  useCallback,
} from 'react';
import * as d3 from 'd3';
import Card from '@mui/material/Card';
import CardContent from '@mui/material/CardContent';
import CardHeader from '@mui/material/CardHeader';
import CardTitle from '@mui/material/Typography';
import Button from '@mui/material/Button';
import { CircularProgress, Box, Typography } from '@mui/material';
import * as PIXI from 'pixi.js';
import '../../../App.css';

// Import modular components
import PixiRenderer from './Renderer/PixiRenderer';
import BraidPoolDAGPixiSocket from './BraidPoolDAGPixiSocket';
import {
  layoutNodesOptimized,
  genColor,
  getSocketUrl,
} from './BraidPoolDAGUtils';
import {
  GraphData,
  NodeIdMapping,
  Position,
  GraphNode,
  ConnectionStatus,
} from './BraidPoolDAGTypes';

// Force software renderer if WebGL fails - compatible approach
try {
  // First check if we can detect WebGL support
  const canvas = document.createElement('canvas');
  const hasWebGL = !!(
    canvas.getContext('webgl') || canvas.getContext('experimental-webgl')
  );

  if (!hasWebGL) {
    console.warn('⚠️ WebGL not detected, forcing software renderer');
    // Different ways to set this depending on PIXI version
    if ((PIXI as any).settings) {
      (PIXI as any).settings.FAIL_IF_MAJOR_PERFORMANCE_CAVEAT = false;
    }

    // For newer PIXI versions
    if ((PIXI as any).utils) {
      (PIXI as any).utils.skipHello();
    }
  }
} catch (e) {
  console.error('Error setting up PIXI renderer fallbacks:', e);
}

// Main component
const GraphVisualizationPixi: React.FC<{ debug?: boolean }> = ({
  debug = false,
}) => {
  // References and state
  const containerRef = useRef<HTMLDivElement>(null);
  const [isMounted, setIsMounted] = useState(false);
  const [graphData, setGraphData] = useState<GraphData | null>(null);
  const [loading, setLoading] = useState(true);
  const [error, setError] = useState<string | null>(null);
  const width = window.innerWidth - 100;
  const height = window.innerHeight;
  const COLORS = [
    0xd95f02, // Orange
    0x7570b3, // Purple
    0x66a61e, // Green
    0xe7298a, // Pink
  ];

  const [nodeIdMap, setNodeIdMap] = useState<NodeIdMapping>({});
  const [selectedCohorts, setSelectedCohorts] = useState<number>(10);
  const [pixi, setPixi] = useState<PIXI.Application | null>(null);
  const [nodeContainer, setNodeContainer] = useState<PIXI.Container | null>(
    null
  );
  const [linkContainer, setLinkContainer] = useState<PIXI.Container | null>(
    null
  );
  const [hiddenContainer, setHiddenContainer] = useState<PIXI.Container | null>(
    null
  );
  const [colorToNode, setColorToNode] = useState<{ [key: string]: any }>({});

  const nodeRadius = 15;
  const margin = useMemo(
    () => ({ top: 20, right: 30, bottom: 30, left: 50 }),
    []
  );
  const COLUMN_WIDTH = 160;
  const VERTICAL_SPACING = 120;

  const [cachedLayout, setCachedLayout] = useState<Record<
    string,
    Position
  > | null>(null);
  const [cachedHwpLength, setCachedHwpLength] = useState<number>(0);

  const tooltipRef = useRef<HTMLDivElement>(null);
  const [connectionStatus, setConnectionStatus] = useState<ConnectionStatus>({
    connected: false,
    status: 'Connecting',
    message: 'Initializing connection...',
  });
  const [totalBeads, setTotalBeads] = useState<number>(0);
  const [totalCohorts, setTotalCohorts] = useState<number>(0);
  const [maxCohortSize, setMaxCohortSize] = useState<number>(0);
  const [hwpLength, setHwpLength] = useState<number>(0);

  // Check when component is mounted
  useEffect(() => {
    console.log('🔄 [PIXI] Main graph component mounted');
    setIsMounted(true);

    // Force container creation if it doesn't exist yet
    if (!containerRef.current) {
      console.log(
        '🔍 [PIXI-Debug] Container ref is null on mount, creating fallback container'
      );
      const fallbackContainer = document.createElement('div');
      fallbackContainer.style.width = '100%';
      fallbackContainer.style.height = '75vh';
      fallbackContainer.style.border = '1px solid #ccc';
      fallbackContainer.id = 'pixi-fallback-container';

      // Add to DOM if needed
      if (document.getElementById('root')) {
        document.getElementById('root')?.appendChild(fallbackContainer);
        containerRef.current = fallbackContainer;
        console.log('🔍 [PIXI-Debug] Created and attached fallback container');
      }
    }

    // Debug check for container visibility on mount
    if (containerRef.current) {
      const containerRect = containerRef.current.getBoundingClientRect();
      console.log('🔍 [PIXI-Debug] Container ref on mount:', {
        width: containerRect.width,
        height: containerRect.height,
        visible: containerRect.width > 0,
        element: containerRef.current,
      });

      // Force container to have dimensions if it doesn't
      if (containerRect.width === 0 || containerRect.height === 0) {
        console.log(
          '🔍 [PIXI-Debug] Container has zero dimensions, forcing size'
        );
        containerRef.current.style.width = `${width}px`;
        containerRef.current.style.height = `${height}px`;
        containerRef.current.style.display = 'block';
      }
    } else {
      console.log('🔍 [PIXI-Debug] Container ref is null on mount');
    }

    // Create tooltip
    if (!document.getElementById('graph-tooltip')) {
      const tooltip = document.createElement('div');
      tooltip.id = 'graph-tooltip';
      tooltip.style.position = 'fixed';
      tooltip.style.visibility = 'hidden';
      tooltip.style.backgroundColor = '#0077B6';
      tooltip.style.color = 'white';
      tooltip.style.border = '1px solid #FF8500';
      tooltip.style.borderRadius = '5px';
      tooltip.style.padding = '10px';
      tooltip.style.boxShadow = '2px 2px 5px rgba(0,0,0,0.2)';
      tooltip.style.pointerEvents = 'none';
      tooltip.style.zIndex = '10000';
      document.body.appendChild(tooltip);
    }

    return () => {
      setIsMounted(false);
      console.log('🔄 [PIXI] Main graph component unmounted');

      // Clean up fallback container if we created one
      const fallbackContainer = document.getElementById(
        'pixi-fallback-container'
      );
      if (fallbackContainer) {
        fallbackContainer.remove();
      }
    };
  }, [width, height]);

  // Update container visibility whenever it changes
  useEffect(() => {
    if (containerRef.current && pixi) {
      const rect = containerRef.current.getBoundingClientRect();
      const isVisible = rect.width > 0 && rect.height > 0;

      // If container becomes visible, force a re-render
      if (isVisible) {
        console.log(
          '🔍 [PIXI-Debug] Container became visible, forcing PIXI render'
        );
        setTimeout(() => {
          pixi.render();
        }, 100);
      }
    }
  }, [pixi]);

  // Handle data received from socket component
  const handleGraphDataLoaded = useCallback(
    (data: GraphData, mapping: NodeIdMapping) => {
      console.log('📊 [PIXI] Graph data received, processing visualization');

      if (
        !data ||
        !data.parents ||
        !data.children ||
        !data.highest_work_path ||
        !data.cohorts
      ) {
        setError('Received invalid data format from server');
        setLoading(false);
        return;
      }

      // Debug Data Structure
      console.log('🔍 [PIXI-Debug] Graph data structure:', {
        parentsCount: Object.keys(data.parents).length,
        childrenCount: Object.keys(data.children).length,
        cohortCount: data.cohorts.length,
        hwpLength: data.highest_work_path.length,
        totalBeads: data.bead_count,
      });

      // Store the data
      setGraphData(data);
      setNodeIdMap(mapping);

      // Extract metrics
      setTotalBeads(data.bead_count || 0);
      setTotalCohorts(data.cohorts.length || 0);

      let maxSize = 0;
      data.cohorts.forEach((cohort) => {
        if (cohort.length > maxSize) maxSize = cohort.length;
      });

      setMaxCohortSize(maxSize);
      setHwpLength(data.highest_work_path.length || 0);
      setLoading(false);

      console.log('✅ [PIXI] Graph data processed and ready for rendering');
    },
    []
  );

  // Handle connection status updates
  const handleConnectionStatusChange = useCallback(
    (status: ConnectionStatus) => {
      setConnectionStatus(status);

      // Update loading state based on connection status
      if (status.status === 'Failed' || status.status === 'Error') {
        setError(status.message);
        setLoading(false);
      }
    },
    []
  );

  // Method to handle when the PIXI app is created
  const handlePixiCreated = useCallback((app: PIXI.Application) => {
    console.log('📱 [PIXI] PIXI application instance stored');

    try {
      setPixi(app);
    } catch (err) {
      console.error('🔍 [PIXI-Debug] Error handling PIXI creation:', err);
    }
  }, []);

  const checkRealWebGLSupport = () => {
    // Most reliable WebGL detection method
    try {
      // Try creating a temporary canvas and getting a WebGL context
      const canvas = document.createElement('canvas');

      // Try WebGL2 first
      let gl = canvas.getContext('webgl2');
      if (gl) {
        console.log('✅ WebGL2 is supported!');
        return {
          supported: true,
          version: 2,
          contextType: 'webgl2',
          renderer: gl.getParameter(gl.RENDERER),
          vendor: gl.getParameter(gl.VENDOR),
        };
      }

      // Fall back to WebGL1
      const gl1 =
        canvas.getContext('webgl') ||
        (canvas.getContext('experimental-webgl') as WebGLRenderingContext);
      if (gl1) {
        console.log('✅ WebGL1 is supported!');
        return {
          supported: true,
          version: 1,
          contextType: 'webgl1',
          renderer: gl1.getParameter(gl1.RENDERER),
          vendor: gl1.getParameter(gl1.VENDOR),
        };
      }

      console.log('❌ WebGL is NOT supported!');
      return { supported: false };
    } catch (e) {
      console.error('❌ Error checking WebGL support:', e);
      return {
        supported: false,
        error: (e as Error).message,
      };
    }
  };

  // Call this before initializing your rendering system
  useEffect(() => {
    const webglSupport = checkRealWebGLSupport();
    console.log('🔍 Definitive WebGL support check:', webglSupport);

    if (!webglSupport.supported) {
      // Show a user-friendly error message about WebGL
      alert(
        'WebGL is not supported in your browser. The graph visualization requires WebGL. Please try a different browser like Chrome or Firefox.'
      );
    }
  }, []);

  if (loading) {
    return (
      <div className='flex items-center justify-center h-full w-full'>
        <div
          ref={containerRef}
          className='flex flex-col items-center'
          style={{
            minHeight: '400px',
            minWidth: '600px',
            width: '100%',
            display: 'flex',
            visibility: 'visible',
          }}>
          <BraidPoolDAGPixiSocket
            onGraphDataLoaded={handleGraphDataLoaded}
            onConnectionStatusChange={handleConnectionStatusChange}
            debug={debug}
          />
          {!connectionStatus.connected && (
            <div style={{ marginTop: '20px' }}>
              <CircularProgress className='h-8 w-8 animate-spin text-[#FF8500]' />
              <p className='mt-4 text-[#0077B6]'>
                {connectionStatus.status === 'Connecting'
                  ? 'Connecting to server...'
                  : 'Loading graph data...'}
              </p>
              <p className='mt-2 text-sm text-gray-500'>
                {connectionStatus.message}
              </p>
            </div>
          )}
        </div>
      </div>
    );
  }

  if (error) {
    return (
      <div className='flex flex-col items-center justify-center h-screen'>
        <div className='text-red-500 mb-4'>Error: {error}</div>
        <p className='text-sm text-gray-500 mb-4'>
          Connection Status: {connectionStatus.status}
        </p>
        <Button onClick={() => window.location.reload()}>Retry</Button>
      </div>
    );
  }

  if (!graphData) {
    return (
      <div className='flex flex-col items-center justify-center h-screen'>
        <div className='text-[#0077B6] mb-4'>No graph data available</div>
        <p className='text-sm text-gray-500 mb-4'>
          Connection Status: {connectionStatus.status}
        </p>
        <Button onClick={() => window.location.reload()}>Refresh</Button>
      </div>
    );
  }

  const forceRender = () => {
    console.log('🔍 [PIXI-Debug] Manual render triggered');
    if (pixi) {
      pixi.render();
    }
  };

  // Function to manually test WebSocket connection
  const testWebSocket = () => {
    console.log('🔍 [PIXI-Debug] Manual WebSocket test triggered');

    // Make basic HTTP request to test server connectivity
    console.log('📡 Testing server connectivity with HTTP request');
    fetch(getSocketUrl(), {
      method: 'GET',
      mode: 'cors',
      cache: 'no-store',
    })
      .then((response) => {
        console.log('✅ Socket server HTTP response:', response.status);
      })
      .catch((err) => {
        console.error('❌ Socket server HTTP test failed:', err);
      });
  };

  return (
    <div className='min-h-screen'>
      <div
        style={{
          margin: '10px',
          position: 'relative',
          display: 'flex',
          gap: '10px',
          alignItems: 'center',
        }}>
        <select
          value={selectedCohorts}
          onChange={(e) => setSelectedCohorts(Number(e.target.value))}
          style={{
            padding: '5px',
            borderRadius: '4px',
            border: '1px solid #0077B6',
            backgroundColor: 'white',
            color: '#0077B6',
          }}>
          {[5, 10, 20, 30, 40, 50, 60, 70, 80, 90, 100].map((value) => (
            <option key={value} value={value}>
              Show latest {value} cohorts
            </option>
          ))}
        </select>
        <Button
          variant='outlined'
          size='small'
          onClick={forceRender}
          style={{ marginRight: '5px', marginLeft: 'auto' }}>
          Force Render
        </Button>
        {debug && (
          <>
            <Button
              variant='outlined'
              color='warning'
              size='small'
              onClick={testWebSocket}>
              Test Socket
            </Button>
            <Button
              variant='outlined'
              color='error'
              size='small'
              onClick={() => {
                console.log('🔍 [Debug] Running basic socket diagnostics');
                // Run basic diagnostics
                fetch(getSocketUrl(), {
                  method: 'GET',
                  mode: 'cors',
                  cache: 'no-store',
                })
                  .then((response) =>
                    console.log(
                      '✅ Server responded with status:',
                      response.status
                    )
                  )
                  .catch((err) =>
                    console.error('❌ Server connection failed:', err)
                  );
              }}>
              Diagnose Connection
            </Button>
          </>
        )}
      </div>

      <div
        data-testid='pixi-container'
        ref={containerRef}
        style={{
          width: '100%',
          height: '75vh',
          border: '1px solid #ccc',
          position: 'relative',
          overflow: 'hidden',
        }}>
        {/* PIXI Canvas will be mounted here */}
        {containerRef.current && (
          <PixiRenderer
            containerElement={containerRef.current}
            graphData={graphData}
            width={width}
            height={height}
            selectedCohorts={selectedCohorts}
            nodeIdMap={nodeIdMap}
            setNodeContainer={setNodeContainer}
            setLinkContainer={setLinkContainer}
            setHiddenContainer={setHiddenContainer}
            onPixiCreated={handlePixiCreated}
          />
        )}
      </div>

      <div
        style={{
          display: 'flex',
          justifyContent: 'space-between',
          margin: '10px',
          padding: '10px',
          backgroundColor: '#f5f5f5',
          borderRadius: '5px',
        }}>
        <div>
          <span
            style={{
              marginRight: '15px',
              fontWeight: 'bold',
              color: '#0077B6',
            }}>
            Beads: {totalBeads}
          </span>
          <span
            style={{
              marginRight: '15px',
              fontWeight: 'bold',
              color: '#0077B6',
            }}>
            Cohorts: {totalCohorts}
          </span>
          <span style={{ fontWeight: 'bold', color: '#0077B6' }}>
            Highest Work Path: {hwpLength} beads
          </span>
        </div>
        <div style={{ color: connectionStatus.connected ? 'green' : 'red' }}>
          {connectionStatus.connected ? '● Connected' : '○ Disconnected'}
        </div>
      </div>
    </div>
  );
};

export default GraphVisualizationPixi;
