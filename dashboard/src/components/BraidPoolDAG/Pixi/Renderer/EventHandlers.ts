import * as PIXI from 'pixi.js';

/**
 * Interface for mouse interaction state and settings
 */
interface InteractionState {
  dragging: boolean;
  lastPosition: { x: number; y: number };
  scale: number;
  minScale: number;
  maxScale: number;
  zoomSpeed: number;
}

/**
 * Sets up all mouse events for panning and zooming
 * @param canvas Canvas element for event binding
 * @param container PIXI container for transformations
 * @returns Cleanup function to remove event listeners
 */
export const setupMouseEvents = (
  canvas: HTMLCanvasElement,
  container: PIXI.Container
) => {
  // Initialize interaction state
  const state: InteractionState = {
    dragging: false,
    lastPosition: { x: 0, y: 0 },
    scale: container.scale.x || 0.25,
    minScale: 0.1,
    maxScale: 5.0,
    zoomSpeed: 1.1,
  };

  // Event handlers optimized for performance
  const handleWheel = (event: WheelEvent) => {
    event.preventDefault();

    // Determine zoom direction
    const delta = event.deltaY > 0 ? 1 / state.zoomSpeed : state.zoomSpeed;

    // Apply zoom with limits
    state.scale *= delta;
    state.scale = Math.max(
      state.minScale,
      Math.min(state.scale, state.maxScale)
    );

    // Update container scale
    container.scale.set(state.scale);

    // Optional: Zoom toward mouse position
    // This would require more complex calculations
  };

  const handleMouseDown = (event: MouseEvent) => {
    state.dragging = true;
    state.lastPosition.x = event.clientX;
    state.lastPosition.y = event.clientY;

    // Change cursor to indicate grabbing
    if (canvas.style) {
      canvas.style.cursor = 'grabbing';
    }
  };

  const handleMouseMove = (event: MouseEvent) => {
    if (!state.dragging) return;

    // Calculate drag distance
    const dx = event.clientX - state.lastPosition.x;
    const dy = event.clientY - state.lastPosition.y;

    // Apply movement, adjusted for scale
    container.position.x += dx / state.scale;
    container.position.y += dy / state.scale;

    // Update last position for next move
    state.lastPosition.x = event.clientX;
    state.lastPosition.y = event.clientY;
  };

  const handleMouseEnd = () => {
    state.dragging = false;

    // Reset cursor
    if (canvas.style) {
      canvas.style.cursor = 'pointer';
    }
  };

  // Add touch support
  const handleTouchStart = (event: TouchEvent) => {
    if (event.touches.length === 1) {
      event.preventDefault();
      state.dragging = true;
      state.lastPosition.x = event.touches[0].clientX;
      state.lastPosition.y = event.touches[0].clientY;
    }
  };

  const handleTouchMove = (event: TouchEvent) => {
    if (!state.dragging || event.touches.length !== 1) return;

    const touch = event.touches[0];
    const dx = touch.clientX - state.lastPosition.x;
    const dy = touch.clientY - state.lastPosition.y;

    container.position.x += dx / state.scale;
    container.position.y += dy / state.scale;

    state.lastPosition.x = touch.clientX;
    state.lastPosition.y = touch.clientY;
  };

  const handleTouchEnd = () => {
    state.dragging = false;
  };

  // Attach all event listeners
  canvas.addEventListener('wheel', handleWheel, { passive: false });
  canvas.addEventListener('mousedown', handleMouseDown);
  canvas.addEventListener('mousemove', handleMouseMove);
  canvas.addEventListener('mouseup', handleMouseEnd);
  canvas.addEventListener('mouseleave', handleMouseEnd);

  // Touch events
  canvas.addEventListener('touchstart', handleTouchStart);
  canvas.addEventListener('touchmove', handleTouchMove);
  canvas.addEventListener('touchend', handleTouchEnd);

  // Return cleanup function
  return () => {
    // Remove all event listeners when done
    canvas.removeEventListener('wheel', handleWheel);
    canvas.removeEventListener('mousedown', handleMouseDown);
    canvas.removeEventListener('mousemove', handleMouseMove);
    canvas.removeEventListener('mouseup', handleMouseEnd);
    canvas.removeEventListener('mouseleave', handleMouseEnd);

    canvas.removeEventListener('touchstart', handleTouchStart);
    canvas.removeEventListener('touchmove', handleTouchMove);
    canvas.removeEventListener('touchend', handleTouchEnd);
  };
};

/**
 * Sets up interactivity on PIXI nodes
 * @param graphics The PIXI graphics object
 * @param nodeData Node data for callbacks
 * @param onClick Click handler callback
 */
export const setupNodeInteractivity = (
  graphics: PIXI.Graphics,
  nodeData: { id: string; [key: string]: any },
  onClick: (nodeId: string, data: any) => void
) => {
  // Make the node interactive
  graphics.eventMode = 'static';
  graphics.cursor = 'pointer';

  // Add a unique id
  graphics.name = nodeData.id;

  // Add click handler
  graphics.on('pointerdown', () => {
    console.log(`🔍 Selected node: ${nodeData.id}`);
    onClick(nodeData.id, nodeData);
  });

  // Optional hover effects
  graphics.on('pointerover', () => {
    // Scale up slightly on hover
    graphics.scale.set(1.2);
  });

  graphics.on('pointerout', () => {
    // Return to normal size
    graphics.scale.set(1.0);
  });
};

export default {
  setupMouseEvents,
  setupNodeInteractivity,
};
