import React from 'react';

/**
 * Interface for debug information to display
 */
interface DebugInfo {
  isWebGLAvailable?: boolean;
  hasInitialized?: boolean;
  canvasAttached?: boolean;
  renderCount?: number;
  lastError?: string | null;
  lastRenderTime?: string;
  fps?: number;
  nodesRendered?: number;
  edgesRendered?: number;
  [key: string]: any;
}

/**
 * A debug overlay component that displays renderer information
 */
const DebugOverlay: React.FC<{ debugInfo: DebugInfo }> = ({ debugInfo }) => {
  // Only show in development environment
  if (process.env.NODE_ENV !== 'development') return null;

  return (
    <div
      style={{
        position: 'absolute',
        bottom: 10,
        right: 10,
        background: 'rgba(0,0,0,0.7)',
        color: 'lime',
        padding: '5px',
        borderRadius: '4px',
        fontSize: '10px',
        fontFamily: 'monospace',
        zIndex: 1000,
        maxWidth: '300px',
        maxHeight: '200px',
        overflow: 'auto',
      }}>
      <div>WebGL: {debugInfo.isWebGLAvailable ? '✅' : '❌'}</div>
      <div>Initialized: {debugInfo.hasInitialized ? '✅' : '❌'}</div>
      <div>Canvas: {debugInfo.canvasAttached ? '✅' : '❌'}</div>
      <div>Renders: {debugInfo.renderCount}</div>
      {debugInfo.nodesRendered && <div>Nodes: {debugInfo.nodesRendered}</div>}
      {debugInfo.edgesRendered && <div>Edges: {debugInfo.edgesRendered}</div>}
      {debugInfo.fps && <div>FPS: {debugInfo.fps.toFixed(1)}</div>}
      {debugInfo.lastError && (
        <div style={{ color: 'red' }}>
          Error: {debugInfo.lastError.toString()}
        </div>
      )}
    </div>
  );
};

/**
 * A debug panel that shows more detailed information
 */
const DebugPanel: React.FC<{
  data: any;
  title?: string;
  isExpanded?: boolean;
  onToggle?: () => void;
}> = ({
  data,
  title = 'Debug Info',
  isExpanded = false,
  onToggle = () => {},
}) => {
  // Only show in development environment
  if (process.env.NODE_ENV !== 'development') return null;

  // Helper function to safely stringify objects that might contain circular references
  const safeStringify = (obj: any, maxLength = 100): string => {
    try {
      // Filter out known problematic properties that might cause circular references
      const getCircularReplacer = () => {
        const seen = new WeakSet();
        return (key: string, value: any) => {
          // Don't try to serialize DOM nodes or PIXI objects that might contain circular references
          if (
            key === 'element' ||
            key === 'pixiAppDetails' ||
            key === 'canvas' ||
            key === 'renderer' ||
            key === 'stage'
          ) {
            return '[Object]';
          }

          // Handle non-objects and null
          if (typeof value !== 'object' || value === null) {
            return value;
          }

          // Handle Date
          if (value instanceof Date) {
            return value.toISOString();
          }

          // Handle arrays
          if (Array.isArray(value)) {
            return value;
          }

          // Handle circular references
          if (seen.has(value)) {
            return '[Circular]';
          }
          seen.add(value);

          return value;
        };
      };

      const stringified = JSON.stringify(obj, getCircularReplacer(), 2);
      return stringified.length > maxLength
        ? stringified.substring(0, maxLength) + '...'
        : stringified;
    } catch (err: any) {
      return `[Error serializing: ${err?.message || 'Unknown error'}]`;
    }
  };

  return (
    <div
      style={{
        position: 'fixed',
        top: 10,
        right: 10,
        zIndex: 9999,
        background: 'rgba(0,0,0,0.8)',
        color: '#00ff00',
        padding: '5px',
        borderRadius: '4px',
        fontFamily: 'monospace',
        fontSize: '10px',
        maxWidth: '300px',
        maxHeight: isExpanded ? '80vh' : '150px',
        overflowY: 'auto',
        transition: 'all 0.3s ease',
      }}>
      <div
        style={{ cursor: 'pointer', fontWeight: 'bold', marginBottom: '5px' }}
        onClick={onToggle}>
        {title} [{isExpanded ? '-' : '+'}]
      </div>
      {Object.entries(data).map(([key, value]) => (
        <div key={key}>
          <strong>{key}:</strong>{' '}
          {typeof value === 'object' ? safeStringify(value) : String(value)}
        </div>
      ))}
    </div>
  );
};

/**
 * FPS Counter component
 */
interface FPSCounterProps {
  visible?: boolean;
}

const FPSCounter: React.FC<FPSCounterProps> = ({ visible = true }) => {
  const [fps, setFps] = React.useState<number>(0);
  const frameTimesRef = React.useRef<number[]>([]);
  const lastFrameTimeRef = React.useRef<number>(performance.now());
  const frameRequestRef = React.useRef<number | null>(null);

  React.useEffect(() => {
    if (!visible) return;

    const updateFPS = () => {
      const now = performance.now();
      const delta = now - lastFrameTimeRef.current;
      lastFrameTimeRef.current = now;

      // Calculate FPS based on frame time
      const currentFPS = 1000 / delta;

      // Keep a rolling window of frame times
      frameTimesRef.current.push(currentFPS);
      if (frameTimesRef.current.length > 60) {
        frameTimesRef.current.shift();
      }

      // Calculate average FPS
      const avgFPS =
        frameTimesRef.current.reduce((sum, value) => sum + value, 0) /
        frameTimesRef.current.length;

      setFps(avgFPS);

      // Request next frame
      frameRequestRef.current = requestAnimationFrame(updateFPS);
    };

    frameRequestRef.current = requestAnimationFrame(updateFPS);

    // Cleanup
    return () => {
      if (frameRequestRef.current !== null) {
        cancelAnimationFrame(frameRequestRef.current);
      }
    };
  }, [visible]);

  if (!visible) return null;

  return (
    <div
      style={{
        position: 'absolute',
        top: 10,
        left: 10,
        backgroundColor: 'rgba(0, 0, 0, 0.5)',
        color: fps > 30 ? '#00ff00' : fps > 15 ? '#ffff00' : '#ff0000',
        padding: '2px 6px',
        borderRadius: '4px',
        fontSize: '10px',
        fontFamily: 'monospace',
        zIndex: 1000,
      }}>
      {fps.toFixed(1)} FPS
    </div>
  );
};

/**
 * A component to display performance metrics for rendering
 */
interface PerformanceMetricsProps {
  renderTime?: number;
  nodeCount?: number;
  edgeCount?: number;
  fps?: number;
  visible?: boolean;
}

const PerformanceMetrics: React.FC<PerformanceMetricsProps> = ({
  renderTime,
  nodeCount,
  edgeCount,
  fps,
  visible = true,
}) => {
  if (!visible || process.env.NODE_ENV !== 'development') return null;

  return (
    <div
      style={{
        position: 'absolute',
        top: 10,
        right: 10,
        backgroundColor: 'rgba(0, 0, 0, 0.7)',
        color: '#ffffff',
        padding: '5px',
        borderRadius: '4px',
        fontSize: '10px',
        fontFamily: 'monospace',
        zIndex: 1000,
      }}>
      <div>
        Render:{' '}
        {renderTime !== undefined ? `${renderTime.toFixed(1)}ms` : 'N/A'}
      </div>
      <div>Nodes: {nodeCount !== undefined ? nodeCount : 'N/A'}</div>
      <div>Edges: {edgeCount !== undefined ? edgeCount : 'N/A'}</div>
      <div>FPS: {fps !== undefined ? fps.toFixed(1) : 'N/A'}</div>
    </div>
  );
};

export { DebugOverlay, DebugPanel, FPSCounter, PerformanceMetrics };
