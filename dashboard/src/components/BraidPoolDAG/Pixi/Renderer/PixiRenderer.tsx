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

    // Add a visible test shape to verify rendering works
    const ctx = canvas.getContext('2d');
    if (ctx) {
      // Draw a visible test rectangle - should be overwritten by PIXI
      ctx.fillStyle = 'rgba(255,0,0,0.5)';
      ctx.fillRect(0, 0, 100, 100);
      console.log(`🧪 [PIXI] Drew test shape on canvas before PIXI init`);
    }

    // Test WebGL context
    const glContext = debugWebGLContext(canvas);
    if (!glContext) {
      setDebugInfo((prev) => ({
        ...prev,
        lastError: 'WebGL context creation failed',
      }));
      console.error(
        '❌ [PIXI] WebGL context creation failed, canvas may not render'
      );
    }

    // Attach canvas to container
    const attached = attachCanvasToContainer(canvas, containerElement);
    setDebugInfo((prev) => ({ ...prev, canvasAttached: attached }));

    // Ensure canvas is visible
    ensureCanvasVisibility(canvas);

    // Create an async initialization function with optimized flow
    const initPixi = async () => {
      try {
        console.log('⏳ [PIXI] Creating PIXI application...');
        const startTime = performance.now();

        // Create and initialize app
        const app = new PIXI.Application();

        // Configure PIXI options with improved context settings
        const pixiOptions = {
          canvas: canvas,
          resolution: Math.min(1.5, window.devicePixelRatio || 1),
          autoDensity: true,
          backgroundColor: 0xffffff,
          antialias: false,
          powerPreference: 'high-performance' as const,
          // Force stencil buffer to avoid masking issues
          stencil: true,
          // Increase precision for better rendering
          precision: 'mediump',
          // Force context preservation
          preserveDrawingBuffer: true,
          // Prevent context loss optimization
          failIfMajorPerformanceCaveat: false,
        };

        console.log('🔍 [DEBUG] Initializing PIXI with options:', pixiOptions);

        // Initialize PIXI
        try {
          await app.init(pixiOptions);
          console.log('🔍 [DEBUG] PIXI init completed successfully');

          // Force a render immediately after initialization
          app.render();
          console.log('🔍 [DEBUG] Initial render completed');
        } catch (initError) {
          console.error('🔍 [DEBUG] PIXI init error:', initError);
          setDebugInfo((prev) => ({
            ...prev,
            lastError: `PIXI init error: ${initError}`,
          }));
          throw initError;
        }

        console.log(
          `✅ [PIXI] App initialized in ${(
            performance.now() - startTime
          ).toFixed(2)}ms`
        );

        // Validate canvas is properly attached
        if (!app.canvas) {
          console.error('🔍 [DEBUG] app.canvas is not available after init!');
          throw new Error('Canvas not attached to PIXI app');
        }

        // Ensure canvas is visible
        ensureCanvasVisibility(app.canvas);
        console.log('🔍 [DEBUG] Canvas visibility ensured. Element details:', {
          width: app.canvas.width,
          height: app.canvas.height,
          style: app.canvas.style,
          parent: app.canvas.parentElement,
        });

        // Store app reference
        appRef.current = app;

        // Create containers
        const mainContainer = new PIXI.Container();
        const links = new PIXI.Container();
        const nodes = new PIXI.Container();
        const hidden = new PIXI.Container();
        hidden.visible = false;

        // Store refs for later use
        nodesContainerRef.current = nodes;
        linksContainerRef.current = links;

        // Setup container hierarchy
        mainContainer.addChild(links, nodes);
        app.stage.addChild(mainContainer, hidden);

        // Setup container interaction
        setupMouseEvents(canvas, mainContainer);

        // Set initial view - position it in the center with a visible scale
        mainContainer.scale.set(0.5); // Increased from 0.25 for better visibility
        mainContainer.position.set(width / 2, height / 2);
        console.log('🔍 [DEBUG] Set initial container position:', {
          x: mainContainer.position.x,
          y: mainContainer.position.y,
          scale: mainContainer.scale.x,
        });

        // Setup interactions on stage
        app.renderer.events.cursorStyles.default = 'pointer';
        app.stage.eventMode = 'static';
        app.stage.cursor = 'pointer';

        // Setup context loss handlers
        setupWebGLContextHandlers(
          app.canvas,
          (event) => {
            console.error('🔍 [PIXI] WebGL context lost event!', event);
            setDebugInfo((prev) => ({
              ...prev,
              lastError: 'WebGL context lost - attempting recovery...',
            }));

            // Add explicit recovery attempt
            setTimeout(() => {
              try {
                console.log('🔄 Attempting WebGL context recovery...');
                if (app && app.renderer) {
                  app.renderer.resize(width, height);
                  app.render();
                  console.log('✅ WebGL context recovered successfully');
                }
              } catch (e) {
                console.error('❌ WebGL recovery failed:', e);
              }
            }, 500);
          },
          () => {
            console.log('🔍 [PIXI] WebGL context restored!');
            if (app) {
              // Force resize and re-render after context restore
              app.renderer.resize(width, height);
              app.render();
              console.log('🔍 [PIXI] Re-rendered after context restore');
            }
          }
        );

        // Force initial render
        app.render();
        console.log('🔍 [DEBUG] Forced renderer to draw initial frame');

        // Store references
        setPixiApp(app);
        setNodeContainer(nodes);
        setLinkContainer(links);
        setHiddenContainer(hidden);
        onPixiCreated(app);

        setDebugInfo((prev) => ({
          ...prev,
          hasInitialized: true,
          renderTimestamp: new Date().toISOString(),
        }));

        console.log(
          `🎉 [PIXI] Total setup time: ${(
            performance.now() - startTime
          ).toFixed(2)}ms`
        );

        // Add a final render after a slight delay to ensure everything is set up
        setTimeout(() => {
          if (app) {
            console.log('🔍 [DEBUG] Running delayed verification render');
            app.render();
          }
        }, 500);
      } catch (err) {
        console.error('❌ [PIXI] Error in PIXI initialization:', err);
        setDebugInfo((prev) => ({
          ...prev,
          lastError: `Initialization error: ${err}`,
        }));
        cleanupResources();
      }
    };

    // Clean up function to avoid code duplication
    const cleanupResources = () => {
      // First destroy PIXI app
      if (appRef.current) {
        try {
          appRef.current.destroy(true);
          appRef.current = null;
        } catch (err) {
          console.error('❌ [PIXI] Cleanup error:', err);
        }
      }

      // Remove canvas from DOM if it exists
      if (canvasRef.current && canvasRef.current.parentElement) {
        console.log('🧹 [PIXI] Removing canvas from DOM during cleanup');
        canvasRef.current.parentElement.removeChild(canvasRef.current);
        canvasRef.current = null;
      }

      // Reset all refs and state
      setNodeContainer(null);
      setLinkContainer(null);
      setHiddenContainer(null);
      setPixiApp(null);
      nodesContainerRef.current = null;
      linksContainerRef.current = null;
    };

    // Start initialization
    initPixi();

    // Cleanup on unmount
    return cleanupResources;
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
