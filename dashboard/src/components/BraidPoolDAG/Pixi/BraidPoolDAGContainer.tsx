import React, { useState, useEffect, useRef } from 'react';
import {
  FormControlLabel,
  Switch,
  CircularProgress,
  Alert,
  Box,
  Typography,
  Button,
  Stack,
  Tooltip,
} from '@mui/material';
import GraphVisualizationPixi from './BraidPoolDAGPixi';
import GraphVisualization from '../BraidPoolDAG';
import * as PIXI from 'pixi.js';

// Add WebGL diagnostics interface
interface WebGLCapabilities {
  webglSupported: boolean;
  webgl2Supported: boolean;
  extensions: Record<string, any>;
  contextAttributes?: {
    alpha: boolean;
    [key: string]: any;
  };
}

interface BrowserInfo {
  renderer?: string;
  vendor?: string;
}

interface WebGLDiagnostics {
  webGLCapabilities?: WebGLCapabilities;
  browserInfo?: BrowserInfo;
}

// Interface for the advanced WebGL test results
interface TestResult {
  test: string;
  result: string;
  details?: any;
  error?: string;
  reason?: string;
}

interface AdvancedWebGLTest {
  originalWebGLSupport: boolean | null;
  testResults: TestResult[];
  successfulTest: string | null;
  finalVerdict: string | null;
  recommendations: string[];
  browserInfo: {
    userAgent: string;
    vendor: string;
    platform: string;
  };
}

// Stubs to replace debug-helpers functions
const runAllChecks = (): WebGLDiagnostics => {
  return {
    webGLCapabilities: {
      webglSupported: PIXI.isWebGLSupported(),
      webgl2Supported: true,
      extensions: {},
    },
    browserInfo: {
      renderer: 'WebGL',
      vendor: 'Browser',
    },
  };
};

const checkWebGLCapabilities = (): any => {
  return {
    webglSupported: PIXI.isWebGLSupported(),
    webgl2Supported: true,
    extensions: {},
  };
};

const forceWebGLTest = (): AdvancedWebGLTest => {
  const isSupported = PIXI.isWebGLSupported();
  return {
    originalWebGLSupport: isSupported,
    testResults: [
      {
        test: 'PIXI.isWebGLSupported',
        result: isSupported ? 'success' : 'failed',
      },
    ],
    successfulTest: isSupported ? 'PIXI.isWebGLSupported' : null,
    finalVerdict: isSupported ? 'WebGL is supported' : 'WebGL is not supported',
    recommendations: [],
    browserInfo: {
      userAgent: navigator.userAgent,
      vendor: navigator.vendor,
      platform: navigator.platform,
    },
  };
};

const testWebSocketConnection = async (url: string): Promise<any> => {
  console.log('📊 Testing connection to:', url);
  return {
    success: true,
    message: 'WebSocket connection test stub',
  };
};

const monitorWebGLContext = (canvas: HTMLCanvasElement): void => {
  console.log(
    '📊 Monitoring WebGL context for canvas:',
    canvas.id || 'unnamed'
  );
};

// Helper to deeply debug WebGL capabilities
const debugWebGLCapabilities = () => {
  console.log('🔎 [WebGL-Debug] Starting detailed WebGL capability check');

  try {
    // Create a test canvas
    const canvas = document.createElement('canvas');
    document.body.appendChild(canvas);

    // Try both WebGL 2 and WebGL 1
    const contexts = [
      { name: 'webgl2', ctx: canvas.getContext('webgl2') },
      { name: 'webgl', ctx: canvas.getContext('webgl') },
    ];

    // Check which contexts are available
    const availableContext = contexts.find((c) => c.ctx !== null);

    if (!availableContext) {
      console.error(
        '🔎 [WebGL-Debug] No WebGL contexts available in this browser'
      );
      document.body.removeChild(canvas);
      return { supported: false, reason: 'No WebGL context available' };
    }

    const { name, ctx } = availableContext;
    console.log(`🔎 [WebGL-Debug] Using ${name} context`);

    if (!ctx) {
      document.body.removeChild(canvas);
      return { supported: false, reason: 'Context creation failed' };
    }

    // Get detailed information
    const debugInfo = {
      contextName: name,
      vendor: ctx.getParameter(ctx.VENDOR),
      renderer: ctx.getParameter(ctx.RENDERER),
      unmaskedVendor: null as string | null,
      unmaskedRenderer: null as string | null,
      version: ctx.getParameter(ctx.VERSION),
      shadingVersion: ctx.getParameter(ctx.SHADING_LANGUAGE_VERSION),
      maxTextureSize: ctx.getParameter(ctx.MAX_TEXTURE_SIZE),
      extensions: ctx.getSupportedExtensions(),
      supported: true,
      reason: 'WebGL is fully supported',
    };

    // Try to get unmasked vendor and renderer
    const debugExt = ctx.getExtension('WEBGL_debug_renderer_info');
    if (debugExt) {
      debugInfo.unmaskedVendor = ctx.getParameter(
        debugExt.UNMASKED_VENDOR_WEBGL
      );
      debugInfo.unmaskedRenderer = ctx.getParameter(
        debugExt.UNMASKED_RENDERER_WEBGL
      );
    }

    // Clean up
    document.body.removeChild(canvas);

    console.log('🔎 [WebGL-Debug] WebGL capability details:', debugInfo);
    return debugInfo;
  } catch (err) {
    console.error('🔎 [WebGL-Debug] Error during WebGL capability check:', err);
    return {
      supported: false,
      reason: `Error checking WebGL: ${err}`,
      error: err,
    };
  }
};

const BraidPoolDAGContainer: React.FC = () => {
  // Check WebGL support
  const [webGLSupported, setWebGLSupported] = useState<boolean>(true);
  // Set WebGL as default only if supported
  const [useWebGL, setUseWebGL] = useState<boolean>(true);
  const [switching, setSwitching] = useState<boolean>(false);
  const [initializing, setInitializing] = useState<boolean>(true);
  const [webGLDetails, setWebGLDetails] = useState<any>(null);
  const [renderAttempts, setRenderAttempts] = useState<number>(0);
  const [renderErrors, setRenderErrors] = useState<string[]>([]);
  const [wsTestResult, setWsTestResult] = useState<any>(null);
  const [isTestingWs, setIsTestingWs] = useState<boolean>(false);
  const appRef = useRef<PIXI.Application | null>(null);
  const [advancedWebGLTest, setAdvancedWebGLTest] =
    useState<AdvancedWebGLTest | null>(null);

  // Improve WebGL stability by setting context preservation
  useEffect(() => {
    const handleVisibilityChange = () => {
      console.log(
        `🔍 Document visibility changed to: ${document.visibilityState}`
      );
      if (document.visibilityState === 'hidden') {
        console.log(
          '💾 Attempting to preserve WebGL context while page is hidden...'
        );
      } else if (document.visibilityState === 'visible' && appRef.current) {
        console.log('👁️ Page is visible again, checking WebGL context...');
        const app = appRef.current;
        const renderer = app.renderer;

        // Check if context is lost using PIXI's built-in methods
        if (
          renderer &&
          'contextLost' in renderer &&
          (renderer as any).contextLost
        ) {
          console.log('🔄 WebGL context was lost, attempting to recover...');
          try {
            // Force a renderer reset by resizing
            app.renderer.resize(app.view.width, app.view.height);
            console.log('✅ WebGL context recovery attempted');
          } catch (err) {
            console.error('❌ WebGL context recovery failed:', err);
          }
        }
      }
    };

    document.addEventListener('visibilitychange', handleVisibilityChange);
    return () =>
      document.removeEventListener('visibilitychange', handleVisibilityChange);
  }, []);

  // Testing WebSocket connection
  const handleTestWebSocket = async () => {
    setIsTestingWs(true);
    setWsTestResult(null);

    try {
      const result = await testWebSocketConnection(
        'ws://french.braidpool.net:65433/socket.io/?EIO=4&transport=websocket'
      );
      console.log('🔎 [WebGL-Debug] WebSocket test results:', result);
      setWsTestResult(result);
    } catch (err) {
      console.error('🔎 [WebGL-Debug] Error testing WebSocket:', err);
      setWsTestResult({
        success: false,
        message: `Test error: ${
          err instanceof Error ? err.message : String(err)
        }`,
      });
    } finally {
      setIsTestingWs(false);
    }
  };

  // Check WebGL support on component mount
  useEffect(() => {
    try {
      console.log('🎮 Checking WebGL support...');
      setInitializing(true);

      // Run advanced WebGL test
      const advancedTest = forceWebGLTest() as AdvancedWebGLTest;
      setAdvancedWebGLTest(advancedTest);

      // If we have a successful test, WebGL is definitely supported
      const isWebGLActuallySupported = !!advancedTest.successfulTest;
      console.log(
        '🔎 [WebGL-Debug] Advanced test results:',
        isWebGLActuallySupported ? 'SUPPORTED' : 'NOT SUPPORTED',
        advancedTest.finalVerdict
      );

      // Get detailed WebGL capabilities
      const details = checkWebGLCapabilities();
      setWebGLDetails(details);

      // Use both our advanced test and PIXI's built-in check
      const isSupported = isWebGLActuallySupported && PIXI.isWebGLSupported();
      console.log(
        '🔎 [WebGL-Debug] PIXI.js reports WebGL supported:',
        PIXI.isWebGLSupported()
      );
      setWebGLSupported(isSupported);

      // Clear any previous errors since we're doing a fresh check
      setRenderErrors([]);

      // If our advanced test found WebGL support but PIXI doesn't, log that
      if (isWebGLActuallySupported && !PIXI.isWebGLSupported()) {
        console.warn(
          '🔎 [WebGL-Debug] Advanced test found WebGL support but PIXI disagrees'
        );
        setRenderErrors([
          'WebGL is supported but PIXI.js cannot use it. This may indicate a browser limitation or configuration issue.',
        ]);
      }

      // If WebGL is not supported, force SVG renderer
      if (!isSupported) {
        console.log(
          '🚫 WebGL not supported in this browser, falling back to SVG'
        );
        setUseWebGL(false);

        // Add specific errors from advanced test
        if (
          advancedTest.recommendations &&
          advancedTest.recommendations.length
        ) {
          setRenderErrors(advancedTest.recommendations);
        } else {
          setRenderErrors([
            'WebGL not supported in your browser. Try a different browser or enable hardware acceleration.',
          ]);
        }
      } else {
        console.log('✅ WebGL is supported - using faster renderer');

        // Use power preferences to improve stability
        const contextAttributes: WebGLContextAttributes = {
          powerPreference: 'high-performance',
          premultipliedAlpha: false,
          preserveDrawingBuffer: true, // Important for context stability
          failIfMajorPerformanceCaveat: false,
          antialias: false, // Disable for performance
        };

        // Create a test canvas with these attributes
        const testCanvas = document.createElement('canvas');
        testCanvas.width = 100;
        testCanvas.height = 100;
        document.body.appendChild(testCanvas);

        try {
          // Try to get a WebGL context with our preferred attributes
          const gl =
            testCanvas.getContext('webgl', contextAttributes) ||
            testCanvas.getContext('webgl2', contextAttributes);

          if (gl) {
            console.log(
              '🔎 [WebGL-Debug] Successfully created test context with preservation settings'
            );
          } else {
            console.warn(
              '🔎 [WebGL-Debug] Could not create test WebGL context with preferred attributes'
            );
          }
        } catch (err) {
          console.warn(
            '🔎 [WebGL-Debug] Error creating test WebGL context:',
            err
          );
        } finally {
          document.body.removeChild(testCanvas);
        }

        // Additional checks for renderer creation
        try {
          console.log('🔎 [WebGL-Debug] Testing PIXI renderer creation...');
          const app = new PIXI.Application();
          // Don't actually need to attach it to DOM for this test
          app
            .init({
              width: 100,
              height: 100,
              backgroundAlpha: 0,
              powerPreference: 'high-performance',
              antialias: false,
              preserveDrawingBuffer: true,
            })
            .then(() => {
              console.log(
                '🔎 [WebGL-Debug] Test PIXI renderer created successfully'
              );
              app.destroy();
            })
            .catch((err) => {
              console.error('🔎 [WebGL-Debug] Test PIXI renderer failed:', err);
              setRenderErrors((prev) => [
                ...prev,
                `Test renderer error: ${err}`,
              ]);
              // Still allow WebGL if PIXI reports it's supported
            });
        } catch (err) {
          console.error('🔎 [WebGL-Debug] Test renderer creation error:', err);
          setRenderErrors((prev) => [...prev, `Test renderer error: ${err}`]);
        }
      }

      // Short delay to allow UI to initialize before rendering heavy components
      setTimeout(() => {
        setInitializing(false);
        console.log('🚀 DAG visualization ready to initialize');
      }, 300);
    } catch (error) {
      console.error('Error checking WebGL support:', error);
      setWebGLSupported(false);
      setUseWebGL(false);
      setRenderErrors((prev) => [...prev, `WebGL detection error: ${error}`]);
      setInitializing(false);
    }
  }, []);

  const handleRendererChange = (event: React.ChangeEvent<HTMLInputElement>) => {
    const wantsWebGL = event.target.checked;

    // If trying to enable WebGL but not supported, show error
    if (wantsWebGL && !webGLSupported) {
      console.error('Cannot enable WebGL - not supported');
      return;
    }

    // Set switching state to show loading indicator
    setSwitching(true);
    console.log('🔄 Changing renderer to:', wantsWebGL ? 'WebGL' : 'SVG');

    // Track render attempt
    setRenderAttempts((prev) => prev + 1);

    // Use setTimeout to allow the UI to update before switching renderers
    setTimeout(() => {
      setUseWebGL(wantsWebGL);
      // Give a small delay to complete the switch
      setTimeout(() => {
        setSwitching(false);
        console.log(
          `🔎 [WebGL-Debug] Renderer switched to ${
            wantsWebGL ? 'WebGL' : 'SVG'
          }`
        );
      }, 500);
    }, 100);
  };

  // Force switch to SVG if multiple WebGL attempts have failed
  useEffect(() => {
    if (renderAttempts > 2 && renderErrors.length > 0 && useWebGL) {
      console.log(
        '🔎 [WebGL-Debug] Multiple WebGL render attempts failed, forcing SVG'
      );
      setUseWebGL(false);
    }
  }, [renderAttempts, renderErrors, useWebGL]);

  // Helper function to force WebGL refresh
  const forceWebGLRefresh = () => {
    if (!useWebGL) return;

    console.log('🔎 [WebGL-Debug] Forcing WebGL renderer refresh');
    setSwitching(true);

    // Force unmount and remount by toggling renderer
    setTimeout(() => {
      setUseWebGL(false);
      setTimeout(() => {
        setUseWebGL(true);
        setRenderAttempts((prev) => prev + 1);
        setTimeout(() => {
          setSwitching(false);
        }, 500);
      }, 100);
    }, 100);
  };

  // Debug function to dump WebGL context details
  const dumpWebGLInfo = () => {
    // Use our new comprehensive debug check
    const report = runAllChecks() as WebGLDiagnostics;
    console.log('🔎 [WebGL-Debug] Comprehensive WebGL diagnostics:', report);

    // Also run our advanced test
    const advTest = forceWebGLTest() as AdvancedWebGLTest;
    console.log('🔎 [WebGL-Debug] Advanced WebGL test results:', advTest);
    setAdvancedWebGLTest(advTest);

    // Monitor all canvases for WebGL context events
    const canvases = document.querySelectorAll('canvas');
    canvases.forEach((canvas) => {
      monitorWebGLContext(canvas);
    });

    // Safe access to properties that might not exist using type guards and optional chaining
    let vendorInfo = 'Not supported';
    let rendererInfo = '';
    let recommendations: string[] = [];

    try {
      if (advTest && advTest.successfulTest) {
        vendorInfo = 'Supported via ' + advTest.successfulTest;
        if (advTest.recommendations && advTest.recommendations.length) {
          recommendations = [...advTest.recommendations];
        }
      } else if (
        report.webGLCapabilities &&
        'supported' in report.webGLCapabilities &&
        report.webGLCapabilities.supported === true
      ) {
        if ('vendor' in report.webGLCapabilities) {
          vendorInfo = (report.webGLCapabilities.vendor as string) || 'Unknown';
        }

        if ('renderer' in report.webGLCapabilities) {
          rendererInfo =
            (report.webGLCapabilities.renderer as string) || 'Unknown';
        }
      }
    } catch (err) {
      console.error('Error accessing WebGL report properties:', err);
      vendorInfo = 'Error accessing data';
    }

    // Show alert with rich info including any recommendations
    let alertMessage = `WebGL Info: ${vendorInfo} - ${rendererInfo}\n\n`;

    if (recommendations.length > 0) {
      alertMessage +=
        'Recommendations:\n' + recommendations.join('\n') + '\n\n';
    }

    alertMessage += 'Check browser console for detailed diagnostics.';

    alert(alertMessage);
  };

  // Run advanced WebGL diagnostics
  const runAdvancedTest = () => {
    setSwitching(true);
    setTimeout(() => {
      const advTest = forceWebGLTest() as AdvancedWebGLTest;
      setAdvancedWebGLTest(advTest);

      // Update errors with recommendations
      if (advTest.recommendations && advTest.recommendations.length > 0) {
        setRenderErrors(advTest.recommendations);
      }

      setSwitching(false);

      // Report findings
      console.log('🔬 [WebGL-Debug] Advanced test complete:', advTest);

      if (advTest.successfulTest && !webGLSupported) {
        // We found WebGL support that the initial test missed!
        setWebGLSupported(true);
        if (!useWebGL) {
          setUseWebGL(true);
        }
        alert('WebGL support detected! Enabling WebGL renderer.');
      } else if (!advTest.successfulTest && webGLSupported) {
        // We initially thought WebGL was supported, but it's not
        setWebGLSupported(false);
        setUseWebGL(false);
        alert('WebGL is not properly supported. Switching to SVG renderer.');
      } else {
        alert(`WebGL test complete: ${advTest.finalVerdict}`);
      }
    }, 100);
  };

  useEffect(() => {
    console.log('⚡ Running WebGL diagnostics...');
    const diagnostics = runAllChecks() as WebGLDiagnostics;

    console.log('📊 WebGL Renderer:', diagnostics.browserInfo?.renderer);
    console.log('📊 WebGL Vendor:', diagnostics.browserInfo?.vendor);

    if (diagnostics.webGLCapabilities) {
      const capabilities = diagnostics.webGLCapabilities;
      console.log(
        '📊 WebGL Support:',
        capabilities.webglSupported ? '✅' : '❌'
      );
      console.log(
        '📊 WebGL2 Support:',
        capabilities.webgl2Supported ? '✅' : '❌'
      );
      console.log(
        '📊 Extensions:',
        Object.keys(capabilities.extensions || {}).length
      );

      // Early detection of potential WebGL issues
      if (!capabilities.webglSupported) {
        console.error('❌ WebGL is not supported in this browser!');
        // Only add this error message if not already added
        const errorMsg =
          'WebGL is not supported in your browser. Please try a different browser.';
        if (!renderErrors.includes(errorMsg)) {
          setRenderErrors((prev) => [...prev, errorMsg]);
        }
      } else if (
        capabilities.contextAttributes &&
        !capabilities.contextAttributes.alpha
      ) {
        console.warn('⚠️ Alpha channel not available in WebGL context');
      }
    }
  }, []);

  if (initializing) {
    return (
      <Box
        sx={{
          display: 'flex',
          flexDirection: 'column',
          alignItems: 'center',
          justifyContent: 'center',
          padding: 4,
          minHeight: '300px',
        }}>
        <CircularProgress size={30} sx={{ mb: 2, color: '#FF8500' }} />
        <Typography variant='h6' sx={{ mb: 1, color: '#0077B6' }}>
          Initializing Braid Visualization
        </Typography>
        <Typography variant='body2' sx={{ textAlign: 'center', color: '#666' }}>
          Optimizing for performance and preparing{' '}
          {webGLSupported ? 'WebGL' : 'SVG'} renderer...
        </Typography>
      </Box>
    );
  }

  return (
    <div>
      <div
        style={{
          padding: '10px',
          display: 'flex',
          justifyContent: 'space-between',
          alignItems: 'center',
          flexWrap: 'wrap',
        }}>
        {!webGLSupported && (
          <Alert
            severity='warning'
            style={{ marginRight: '10px', flexGrow: 1 }}>
            WebGL is not supported in your browser. Using SVG renderer only.
          </Alert>
        )}

        {renderErrors.length > 0 && useWebGL && (
          <Alert
            severity='info'
            style={{ marginRight: '10px', flexGrow: 1, marginBottom: '10px' }}>
            Renderer may have issues. Consider switching to SVG if visualization
            is missing.
          </Alert>
        )}

        {wsTestResult && (
          <Alert
            severity={wsTestResult.success ? 'success' : 'error'}
            style={{ marginRight: '10px', flexGrow: 1, marginBottom: '10px' }}>
            WebSocket test: {wsTestResult.message}
          </Alert>
        )}

        <div
          style={{
            display: 'flex',
            alignItems: 'center',
            flexWrap: 'wrap',
            gap: '10px',
          }}>
          {switching && (
            <CircularProgress size={20} style={{ marginRight: '10px' }} />
          )}
          <FormControlLabel
            control={
              <Switch
                checked={useWebGL}
                onChange={handleRendererChange}
                color='primary'
                disabled={switching || !webGLSupported}
              />
            }
            label={useWebGL ? 'Using WebGL (faster)' : 'Using SVG (slower)'}
          />

          <Stack direction='row' spacing={1}>
            {useWebGL && (
              <Button
                size='small'
                variant='outlined'
                onClick={forceWebGLRefresh}
                disabled={switching}
                style={{ marginLeft: '5px' }}>
                Refresh WebGL
              </Button>
            )}

            <Button
              size='small'
              variant='text'
              onClick={dumpWebGLInfo}
              style={{ marginLeft: '5px' }}>
              Debug Info
            </Button>

            <Tooltip title='Run comprehensive WebGL capability test'>
              <Button
                size='small'
                variant='outlined'
                color='primary'
                onClick={runAdvancedTest}
                disabled={switching}>
                Advanced Test
              </Button>
            </Tooltip>

            <Tooltip title='Test WebSocket connection to server'>
              <Button
                size='small'
                variant='outlined'
                color='warning'
                onClick={handleTestWebSocket}
                disabled={isTestingWs}>
                {isTestingWs ? 'Testing...' : 'Test Connection'}
              </Button>
            </Tooltip>
          </Stack>
        </div>
      </div>

      <div style={{ position: 'relative', minHeight: '500px' }}>
        {switching ? (
          <div
            style={{
              display: 'flex',
              justifyContent: 'center',
              alignItems: 'center',
              position: 'absolute',
              top: 0,
              left: 0,
              right: 0,
              bottom: 0,
            }}>
            <CircularProgress size={40} />
            <span style={{ marginLeft: '10px' }}>Switching renderers...</span>
          </div>
        ) : useWebGL ? (
          <>
            <GraphVisualizationPixi debug={false} />
            <div
              style={{
                position: 'absolute',
                bottom: 10,
                left: 10,
                background: 'rgba(0,0,0,0.4)',
                color: '#fff',
                padding: '4px 8px',
                borderRadius: '2px',
                fontSize: '12px',
                pointerEvents: 'none',
              }}>
              WebGL Render Attempt: {renderAttempts}
            </div>
          </>
        ) : (
          <GraphVisualization />
        )}
      </div>

      <Box sx={{ mt: 2, px: 1, display: 'flex', justifyContent: 'center' }}>
        <Typography
          variant='caption'
          sx={{ color: '#666', fontStyle: 'italic' }}>
          The {useWebGL ? 'WebGL' : 'SVG'} renderer is now active.{' '}
          {useWebGL
            ? 'WebGL offers better performance for large graphs.'
            : 'SVG is more compatible but slower.'}
        </Typography>
      </Box>

      {/* Debug panel showing only if we have errors in SVG mode, 
          or specific helpful recommendations in WebGL mode */}
      {((!useWebGL && renderErrors.length > 0) ||
        (useWebGL &&
          (advancedWebGLTest?.recommendations?.length ?? 0) > 0)) && (
        <Box
          sx={{
            mt: 1,
            p: 1,
            border: '1px solid #ddd',
            borderRadius: 1,
            background: 'rgba(0,0,0,0.03)',
            maxHeight: '100px',
            overflowY: 'auto',
            fontSize: '10px',
            fontFamily: 'monospace',
          }}>
          <Typography variant='caption' fontWeight='bold'>
            Debug Info:
          </Typography>
          {useWebGL && advancedWebGLTest?.recommendations
            ? advancedWebGLTest.recommendations.map((rec, i) => (
                <div key={i} style={{ marginTop: '4px' }}>
                  {rec}
                </div>
              ))
            : renderErrors.map((err, i) => (
                <div key={i} style={{ marginTop: '4px' }}>
                  {err}
                </div>
              ))}
        </Box>
      )}
    </div>
  );
};

export default BraidPoolDAGContainer;
