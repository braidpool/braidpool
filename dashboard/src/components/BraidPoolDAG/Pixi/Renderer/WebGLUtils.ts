/**
 * Simple implementation of the WebGL capability checker
 */
const checkWebGLCapabilities = () => {
  try {
    const canvas = document.createElement('canvas');
    const gl = canvas.getContext('webgl') || canvas.getContext('webgl2');

    if (!gl) {
      return {
        webglSupported: false,
        webgl2Supported: false,
        extensions: {},
        supported: false,
      };
    }

    return {
      webglSupported: !!canvas.getContext('webgl'),
      webgl2Supported: !!canvas.getContext('webgl2'),
      extensions: gl.getSupportedExtensions() || [],
      supported: true,
    };
  } catch (err) {
    console.error('Error checking WebGL capabilities:', err);
    return {
      webglSupported: false,
      webgl2Supported: false,
      extensions: {},
      supported: false,
    };
  }
};

/**
 * Monitors a canvas for WebGL context events
 */
const monitorWebGLContext = (canvas: HTMLCanvasElement) => {
  // Simple implementation that just adds event listeners
  canvas.addEventListener('webglcontextlost', (e) => {
    console.log('📊 WebGL context lost on canvas:', canvas.id || 'unnamed');
  });

  canvas.addEventListener('webglcontextrestored', () => {
    console.log('📊 WebGL context restored on canvas:', canvas.id || 'unnamed');
  });
};

/**
 * Debug helper function for WebGL context
 * @param canvas HTML Canvas element to test
 * @returns WebGL context or null if unavailable
 */
export const debugWebGLContext = (canvas: HTMLCanvasElement | null) => {
  if (!canvas) {
    console.error('🔍 [DEBUG] Canvas element is null!');
    return null;
  }

  try {
    // Try to get WebGL context and check capabilities
    const gl = canvas.getContext('webgl2') || canvas.getContext('webgl');

    if (!gl) {
      console.error('🔍 [DEBUG] Failed to obtain WebGL context from canvas!');
      return null;
    }

    // Debug WebGL capabilities
    const debugInfo = {
      vendor: gl.getParameter(gl.VENDOR),
      renderer: gl.getParameter(gl.RENDERER),
      version: gl.getParameter(gl.VERSION),
      shadingLanguageVersion: gl.getParameter(gl.SHADING_LANGUAGE_VERSION),
      maxTextureSize: gl.getParameter(gl.MAX_TEXTURE_SIZE),
      extensions: gl.getSupportedExtensions(),
    };

    console.log('🔍 [DEBUG] WebGL Context Details:', debugInfo);
    return gl;
  } catch (e) {
    console.error('🔍 [DEBUG] WebGL context creation error:', e);
    return null;
  }
};

/**
 * Sets up WebGL context loss handling for a canvas
 * @param canvas Canvas element to monitor
 * @param onLost Callback when context is lost
 * @param onRestored Callback when context is restored
 */
export const setupWebGLContextHandlers = (
  canvas: HTMLCanvasElement | null,
  onLost: (event: Event) => void,
  onRestored: () => void
) => {
  if (!canvas) return;

  // Start monitoring the canvas for WebGL context events
  monitorWebGLContext(canvas);

  // Add WebGL context loss handler
  canvas.addEventListener('webglcontextlost', (event) => {
    event.preventDefault(); // Critical to allow context restoration!
    console.error('🔍 [PIXI] WebGL context lost!', event);
    onLost(event);
  });

  canvas.addEventListener('webglcontextrestored', () => {
    console.log('🔍 [PIXI] WebGL context restored!');
    onRestored();
  });
};

/**
 * Checks WebGL support and capabilities of the browser
 * @returns Object with WebGL support information
 */
export const checkWebGLSupport = () => {
  console.log('🔍 [DEBUG] WebGL Support Check');

  const result = {
    isSupported: false,
    capabilities: null as ReturnType<typeof checkWebGLCapabilities> | null,
    testCanvas: null as HTMLCanvasElement | null,
  };

  try {
    // Use the local implementation of checkWebGLCapabilities
    result.capabilities = checkWebGLCapabilities();
    result.isSupported =
      result.capabilities && (result.capabilities as any).supported;

    // Create a test canvas and try to get a context directly
    const testCanvas = document.createElement('canvas');
    testCanvas.width = 1;
    testCanvas.height = 1;
    result.testCanvas = testCanvas;

    const gl =
      testCanvas.getContext('webgl2') || testCanvas.getContext('webgl');
    result.isSupported = result.isSupported && !!gl;

    return result;
  } catch (err) {
    console.error('🔍 [DEBUG] Error during WebGL support check:', err);
    return result;
  }
};

export default {
  debugWebGLContext,
  setupWebGLContextHandlers,
  checkWebGLSupport,
};
