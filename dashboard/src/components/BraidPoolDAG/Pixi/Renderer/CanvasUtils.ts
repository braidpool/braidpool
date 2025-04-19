/**
 * Helper functions for managing canvas elements
 */

/**
 * Ensures a canvas is visible in the DOM with proper dimensions
 * @param canvas Canvas element to check and make visible
 */
export const ensureCanvasVisibility = (canvas: HTMLCanvasElement | null) => {
  if (!canvas) return;

  // Make sure canvas is displayed correctly
  canvas.style.display = 'block';

  // Ensure canvas has explicit dimensions
  if (!canvas.style.width) {
    canvas.style.width = `${canvas.width}px`;
  }

  if (!canvas.style.height) {
    canvas.style.height = `${canvas.height}px`;
  }

  // Verify visibility after a short delay
  setTimeout(() => {
    if (canvas && document.body.contains(canvas)) {
      const rect = canvas.getBoundingClientRect();
      console.log('🔍 [DEBUG] Canvas visibility check:', {
        width: canvas.width,
        height: canvas.height,
        clientWidth: rect.width,
        clientHeight: rect.height,
        display: canvas.style.display,
        visible: rect.width > 0 && rect.height > 0,
        inDOM: document.body.contains(canvas),
      });

      if (rect.width === 0 || rect.height === 0) {
        console.warn('⚠️ [DEBUG] Canvas has zero dimensions in the DOM!');
        // Try to force dimensions
        canvas.style.width = `${canvas.width || 100}px`;
        canvas.style.height = `${canvas.height || 100}px`;
        canvas.style.position = 'absolute';
        canvas.style.zIndex = '1000';
      }
    }
  }, 100);
};

/**
 * Creates a properly configured canvas element for WebGL use
 * @param width Canvas width
 * @param height Canvas height
 * @param id Optional ID for the canvas
 * @returns Configured canvas element
 */
export const createPIXICanvas = (
  width: number,
  height: number,
  id?: string
) => {
  const canvas = document.createElement('canvas');

  // Set dimensions with sensible defaults
  canvas.width = width || window.innerWidth;
  canvas.height = height || window.innerHeight;

  // Configure styling for proper display
  canvas.style.display = 'block';
  canvas.style.width = `${canvas.width}px`;
  canvas.style.height = `${canvas.height}px`;

  // Add debugging attributes
  canvas.setAttribute('data-debug', 'pixi-renderer-canvas');
  if (id) {
    canvas.id = id;
  }

  return canvas;
};

/**
 * Attach a canvas to a container element
 * @param canvas Canvas to attach
 * @param container Container element
 * @returns Boolean indicating success
 */
export const attachCanvasToContainer = (
  canvas: HTMLCanvasElement,
  container: HTMLElement
) => {
  if (!canvas || !container) {
    console.error('🔍 [DEBUG] Invalid canvas or container');
    return false;
  }

  try {
    // First check for existing canvases and remove them
    const existingCanvases = container.querySelectorAll('canvas');
    if (existingCanvases.length > 0) {
      console.log(
        `🔍 [DEBUG] Removing ${existingCanvases.length} existing canvas elements`
      );
      existingCanvases.forEach((oldCanvas) => {
        if (oldCanvas.id === canvas.id) {
          container.removeChild(oldCanvas);
        }
      });
    }

    // Add our canvas
    container.appendChild(canvas);
    console.log('🔍 [DEBUG] Canvas attached to DOM');
    return true;
  } catch (err) {
    console.error('🔍 [DEBUG] Error attaching canvas to container:', err);
    return false;
  }
};

/**
 * Diagnoses issues with the canvas element
 * @param canvas Canvas to diagnose
 * @returns Diagnostic information
 */
export const diagnoseCanvasIssues = (canvas: HTMLCanvasElement | null) => {
  if (!canvas) {
    return { valid: false, reason: 'Canvas is null' };
  }

  const result = {
    valid: true,
    inDOM: document.body.contains(canvas),
    visible: false,
    dimensions: {
      width: canvas.width,
      height: canvas.height,
      styleWidth: canvas.style.width,
      styleHeight: canvas.style.height,
    },
    displayStyle: canvas.style.display,
    position: canvas.style.position,
    issues: [] as string[],
  };

  // Check if dimensions are valid
  if (canvas.width === 0 || canvas.height === 0) {
    result.valid = false;
    result.issues.push('Canvas has zero width or height');
  }

  // Check if the canvas is actually visible
  const rect = canvas.getBoundingClientRect();
  result.visible = rect.width > 0 && rect.height > 0;

  if (!result.visible) {
    result.issues.push('Canvas has no visible area (width/height might be 0)');
  }

  if (!result.inDOM) {
    result.valid = false;
    result.issues.push('Canvas is not attached to the DOM');
  }

  return result;
};

export default {
  ensureCanvasVisibility,
  createPIXICanvas,
  attachCanvasToContainer,
  diagnoseCanvasIssues,
};
