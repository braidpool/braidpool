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

      // Process the graph data with selectedCohorts parameter
      const { nodeList, hwpSet } = processGraphData(graphData, selectedCohorts);

      if (nodeList.length === 0) {
        console.warn('⚠️ [PIXI] No nodes to render');
        return;
      }

      // Create cohort map for proper coloring
      const cohortMap = new Map<string, number>();
      (graphData.cohorts || []).forEach((cohort, index) => {
        cohort.forEach((nodeId) => cohortMap.set(nodeId, index));
      });

      // Calculate node positions
      const positions = layoutNodesOptimized(
        nodeList,
        graphData.highest_work_path || [],
        graphData.cohorts || [],
        selectedCohorts,
        width,
        height,
        { top: 20, right: 30, bottom: 30, left: 50 },
        120, // COLUMN_WIDTH
        100, // VERTICAL_SPACING
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
        handleNodeClick,
        cohortMap,
        selectedCohorts,
        graphData.cohorts?.length || 0
      );

      // Calculate bounds of the entire graph to position camera
      if (nodeCount > 0) {
        console.log('🔍 Attempting to position viewport to show graph');

        // Find the bounds of all nodes
        let minX = Infinity,
          minY = Infinity;
        let maxX = -Infinity,
          maxY = -Infinity;

        Object.values(positions).forEach((pos) => {
          minX = Math.min(minX, pos.x);
          minY = Math.min(minY, pos.y);
          maxX = Math.max(maxX, pos.x);
          maxY = Math.max(maxY, pos.y);
        });

        console.log(
          `📏 Original graph bounds: (${minX},${minY}) to (${maxX},${maxY})`
        );

        // IMPORTANT: Check if the graph is too wide (which causes extreme scaling)
        const graphWidth = maxX - minX + 100;
        const graphHeight = maxY - minY + 100;

        // If width is extremely large compared to height, compress the layout
        const compressionNeeded = graphWidth > 10000;
        if (compressionNeeded) {
          console.log(
            `⚠️ Graph is extremely wide (${graphWidth}px), compressing x-coordinates`
          );

          // Compress all positions to a reasonable range
          const targetWidth = 3000; // A more reasonable width
          const compressionFactor = targetWidth / graphWidth;

          Object.keys(positions).forEach((nodeId) => {
            // Compress x coordinates only
            positions[nodeId].x =
              minX + (positions[nodeId].x - minX) * compressionFactor;
          });

          // Recalculate bounds after compression
          minX = Infinity;
          minY = Infinity;
          maxX = -Infinity;
          maxY = -Infinity;

          Object.values(positions).forEach((pos) => {
            minX = Math.min(minX, pos.x);
            minY = Math.min(minY, pos.y);
            maxX = Math.max(maxX, pos.x);
            maxY = Math.max(maxY, pos.y);
          });

          console.log(
            `📏 Compressed graph bounds: (${minX},${minY}) to (${maxX},${maxY})`
          );
        }

        // Calculate dimensions with potentially compressed coordinates
        const finalGraphWidth = maxX - minX + 100;
        const finalGraphHeight = maxY - minY + 100;

        // Get the parent container
        const mainContainer = nodesContainerRef.current?.parent;

        if (mainContainer) {
          // Reset position and scale first
          mainContainer.position.set(0, 0);
          mainContainer.scale.set(1);

          // Calculate optimal scale to fit within viewport
          const scaleX = width / finalGraphWidth;
          const scaleY = height / finalGraphHeight;
          const scale = Math.min(scaleX, scaleY, 0.9); // Limit max scale to 0.9

          // Apply scale
          mainContainer.scale.set(scale);

          // Center graph in viewport
          const centerX = minX + finalGraphWidth / 2;
          const centerY = minY + finalGraphHeight / 2;

          // Set position (accounting for scale)
          mainContainer.position.x = width / 2 - centerX * scale;
          mainContainer.position.y = height / 2 - centerY * scale;

          console.log(
            `🎯 Positioned viewport: scale=${scale}, pos=(${mainContainer.position.x}, ${mainContainer.position.y})`
          );
        }
      }

      // Force a render ONLY if pixiApp exists
      if (pixiApp && pixiApp.renderer) {
        pixiApp.render();
      }

      // Update metrics
      const renderTime = performance.now() - renderStartTime;
      setPerformanceMetrics({
        renderTime,
        nodeCount: nodeCount,
        edgeCount: edgeCount,
        fps: parseFloat((1000 / renderTime).toFixed(2)),
      });

      // Update debug info
      setDebugInfo((prev) => ({
        ...prev,
        nodesRendered: nodeCount,
        edgesRendered: edgeCount,
      }));

      console.log(
        `✅ [PIXI] Graph render completed in ${renderTime.toFixed(2)}ms`
      );
    } catch (err) {
      console.error('❌ [PIXI] Error rendering graph:', err);
      setDebugInfo((prev) => ({
        ...prev,
        lastError: `Render error: ${err}`,
      }));
    }
  }, [
    pixiApp,
    graphData,
    width,
    height,
    cachedLayout,
    cachedHwpLength,
    selectedCohorts,
    setCachedLayout,
    setCachedHwpLength,
  ]);

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
