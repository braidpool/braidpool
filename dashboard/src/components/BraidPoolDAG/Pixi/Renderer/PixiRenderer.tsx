import React, { useEffect, useRef, useState } from 'react';
import * as PIXI from 'pixi.js';
// No need to import events separately in PIXI v8
// import '@pixi/events';
import { PixiRendererProps, GraphNode, Position } from '../BraidPoolDAGTypes';
import { genColor, layoutNodesOptimized } from '../BraidPoolDAGUtils';

// Import modular components
import { debugWebGLContext, setupWebGLContextHandlers } from './WebGLUtils';
import {
  createPIXICanvas,
  ensureCanvasVisibility,
  attachCanvasToContainer,
} from './CanvasUtils';
import { setupMouseEvents } from './EventHandlers';
import { processGraphData, renderEdges, renderNodes } from './RenderUtils';
import {
  DebugOverlay,
  FPSCounter,
  PerformanceMetrics,
} from './DebugComponents';

/**
 * Main PIXI Renderer component
 * Handles WebGL initialization, graph rendering, and interactions
 */
const PixiRenderer: React.FC<PixiRendererProps> = ({
  containerElement,
  graphData,
  width,
  height,
  selectedCohorts,
  nodeIdMap,
  setNodeContainer,
  setLinkContainer,
  setHiddenContainer,
  onPixiCreated,
}) => {
  // State
  const [pixiApp, setPixiApp] = useState<PIXI.Application | null>(null);
  const [performanceMetrics, setPerformanceMetrics] = useState({
    renderTime: 0,
    nodeCount: 0,
    edgeCount: 0,
    fps: 0,
  });

  // Refs
  const appRef = useRef<PIXI.Application | null>(null);
  const canvasRef = useRef<HTMLCanvasElement | null>(null);
  const nodesContainerRef = useRef<PIXI.Container | null>(null);
  const linksContainerRef = useRef<PIXI.Container | null>(null);

  // For layout caching
  const [cachedLayout, setCachedLayout] = useState<Record<
    string,
    Position
  > | null>(null);
  const [cachedHwpLength, setCachedHwpLength] = useState<number>(0);

  // Debug state
  const [debugInfo, setDebugInfo] = useState({
    isWebGLAvailable: PIXI.isWebGLSupported(),
    hasInitialized: false,
    canvasAttached: false,
    renderCount: 0,
    lastError: null as string | null,
    lastRenderTime: '',
    nodesRendered: 0,
    edgesRendered: 0,
  });

  // Handle node click events
  const handleNodeClick = (nodeId: string, nodeData: GraphNode) => {
    console.log(`🔍 Selected node: ${nodeId}`, nodeData);
    // Implement node selection logic here
  };

  // Initialize PIXI - this only runs once when the component mounts
  useEffect(() => {
    console.log('🚀 [PIXI] PixiRenderer starting initialization');
    console.log('🔍 [DEBUG] WebGL Support:', PIXI.isWebGLSupported());

    // Validate container element
    if (!containerElement) {
      console.error('❌ [PIXI] Container element is invalid');
      setDebugInfo((prev) => ({
        ...prev,
        lastError: 'Invalid container element',
      }));
      return;
    }

    // Create canvas
    const canvas = createPIXICanvas(width, height, 'pixi-renderer-canvas');
    canvasRef.current = canvas;

    // Force canvas to have actual dimensions
    canvas.width = width > 0 ? width : 800;
    canvas.height = height > 0 ? height : 600;
    canvas.style.width = `${canvas.width}px`;
    canvas.style.height = `${canvas.height}px`;
    canvas.style.display = 'block';

    // Attach canvas to DOM
    attachCanvasToContainer(canvas, containerElement);

    // Update debug info
    setDebugInfo((prev) => ({
      ...prev,
      canvasAttached: true,
    }));

    console.log('📌 Canvas attached to container');

    // Initialize PIXI
    const initPixi = async () => {
      const startTime = performance.now();
      try {
        // Create application with proper settings
        const app = new PIXI.Application();
        await app.init({
          canvas,
          width,
          height,
          antialias: true,
          resolution: window.devicePixelRatio || 1,
          autoDensity: true,
          backgroundAlpha: 1,
        });

        console.log('✅ [PIXI] Application initialized successfully');

        // Set up main containers
        const mainContainer = new PIXI.Container();
        app.stage.addChild(mainContainer);

        // Create nodes container
        const nodesContainer = new PIXI.Container();
        mainContainer.addChild(nodesContainer);
        nodesContainerRef.current = nodesContainer;

        // Create links container
        const linksContainer = new PIXI.Container();
        mainContainer.addChild(linksContainer);
        linksContainerRef.current = linksContainer;

        // Create hidden hit area container
        const hiddenContainer = new PIXI.Container();
        mainContainer.addChild(hiddenContainer);

        // Set containers for parent component access
        if (setNodeContainer) setNodeContainer(nodesContainer);
        if (setLinkContainer) setLinkContainer(linksContainer);
        if (setHiddenContainer) setHiddenContainer(hiddenContainer);

        // Set interactive mode
        mainContainer.eventMode = 'static';

        // Add pan and zoom functionality
        setupMouseEvents(canvas, app);

        // Update refs and state
        appRef.current = app;
        setPixiApp(app);
        setDebugInfo((prev) => ({
          ...prev,
          hasInitialized: true,
          lastError: null,
        }));

        console.log(
          `🎮 [PIXI] Setup complete in ${(
            performance.now() - startTime
          ).toFixed(2)}ms`
        );

        // Notify parent when PIXI is created
        if (onPixiCreated) onPixiCreated(app);

        // Initial render
        app.render();
      } catch (err) {
        console.error('❌ [PIXI] Initialization error:', err);
        setDebugInfo((prev) => ({
          ...prev,
          hasInitialized: false,
          lastError: `Init error: ${err}`,
        }));
      }
    };

    // Call initPixi
    initPixi();

    // Cleanup function
    return () => {
      console.log('🧹 [PIXI] Cleaning up resources');
      if (appRef.current) {
        console.log('🛑 [PIXI] Destroying PIXI application');
        appRef.current.destroy();
        appRef.current = null;
        setPixiApp(null);
      }
      if (canvasRef.current && containerElement.contains(canvasRef.current)) {
        containerElement.removeChild(canvasRef.current);
      }
    };
  }, [
    containerElement,
    width,
    height,
    onPixiCreated,
    setNodeContainer,
    setLinkContainer,
    setHiddenContainer,
  ]);

  // Effect to handle graph data updates - this renders the graph
  useEffect(() => {
    if (
      !pixiApp ||
      !graphData ||
      !nodesContainerRef.current ||
      !linksContainerRef.current
    ) {
      return;
    }

    const renderStartTime = performance.now();
    console.log(
      '🎨 [PIXI] Rendering graph with',
      graphData.bead_count || 0,
      'nodes'
    );

    // Update debug render state
    setDebugInfo((prev) => ({
      ...prev,
      renderCount: prev.renderCount + 1,
      lastRenderTime: new Date().toISOString(),
    }));

    try {
      // Validate renderer state
      if (!pixiApp.renderer) {
        throw new Error('Renderer is null, WebGL context may be lost');
      }

      // Ensure canvas is visible
      if (pixiApp.canvas) {
        ensureCanvasVisibility(pixiApp.canvas);
      } else {
        throw new Error('Canvas is null, WebGL context may be lost');
      }

      // Process the graph data
      const { nodeList, hwpSet } = processGraphData(graphData);

      if (nodeList.length === 0) {
        console.warn('⚠️ [PIXI] No nodes to render');
        return;
      }

      // Calculate node positions
      const positions = layoutNodesOptimized(
        nodeList,
        graphData.highest_work_path || [],
        graphData.cohorts || [],
        selectedCohorts,
        width,
        height,
        { top: 50, right: 50, bottom: 50, left: 50 },
        80, // Column width
        30, // Vertical spacing
        cachedLayout,
        cachedHwpLength,
        setCachedLayout,
        setCachedHwpLength
      );

      // Render edges first (behind nodes)
      const edgeCount = renderEdges(
        nodeList,
        positions,
        hwpSet,
        linksContainerRef.current
      );

      // Render nodes
      const nodeCount = renderNodes(
        nodeList,
        positions,
        hwpSet,
        nodesContainerRef.current,
        handleNodeClick
      );

      // Add this block: Position view to show the entire graph
      if (nodeCount > 0 && (nodesContainerRef.current as any).graphBoundaries) {
        const bounds = (nodesContainerRef.current as any).graphBoundaries;
        const graphWidth = (nodesContainerRef.current as any).graphWidth;
        const graphHeight = (nodesContainerRef.current as any).graphHeight;

        // Get the parent container
        const mainContainer = nodesContainerRef.current.parent;

        if (mainContainer) {
          console.log(`🔍 [PIXI] Positioning viewport to show graph`);

          // Calculate optimal scale to fit
          const scaleX = (width * 0.8) / graphWidth;
          const scaleY = (height * 0.8) / graphHeight;
          const scale = Math.min(scaleX, scaleY, 1.0); // Limit max scale to 1.0

          // Apply scale
          mainContainer.scale.set(scale);

          // Center graph in viewport
          const centerX = bounds.minX + graphWidth / 2;
          const centerY = bounds.minY + graphHeight / 2;

          // Set position (accounting for scale)
          mainContainer.position.x = width / 2 - centerX * scale;
          mainContainer.position.y = height / 2 - centerY * scale;

          console.log(
            `🎯 [PIXI] Viewport positioned: scale=${scale}, pos=(${mainContainer.position.x}, ${mainContainer.position.y})`
          );
        }
      }

      // Update metrics
      const renderTime = performance.now() - renderStartTime;
      setPerformanceMetrics({
        renderTime,
        nodeCount,
        edgeCount,
        fps: 1000 / renderTime, // Simple FPS estimate
      });

      setDebugInfo((prev) => ({
        ...prev,
        nodesRendered: nodeCount,
        edgesRendered: edgeCount,
      }));

      // Render scene
      pixiApp.render();
      console.log(`✅ [PIXI] Graph rendered in ${renderTime.toFixed(2)}ms`);
    } catch (err) {
      console.error('❌ [PIXI] Error rendering graph:', err);
      setDebugInfo((prev) => ({
        ...prev,
        lastError: `Graph error: ${err}`,
      }));
    }
  }, [pixiApp, graphData, selectedCohorts, width, height]);

  return (
    <>
      {/* Debug components */}
      {process.env.NODE_ENV === 'development' && (
        <>
          <DebugOverlay debugInfo={debugInfo} />
          <FPSCounter visible={true} />
          <PerformanceMetrics
            renderTime={performanceMetrics.renderTime}
            nodeCount={performanceMetrics.nodeCount}
            edgeCount={performanceMetrics.edgeCount}
            fps={performanceMetrics.fps}
            visible={true}
          />
        </>
      )}
    </>
  );
};

export default PixiRenderer;
