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
 * @param app PIXI application for transformations
 * @returns Cleanup function to remove event listeners
 */
export function setupMouseEvents(
  canvas: HTMLCanvasElement,
  app: PIXI.Application
) {
  console.log('🖱️ Setting up mouse events on canvas');

  let isDragging = false;
  let lastPosition = { x: 0, y: 0 };

  // Zoom functionality
  canvas.addEventListener('wheel', (e) => {
    e.preventDefault();

    // Get mouse position
    const rect = canvas.getBoundingClientRect();
    const mouseX = e.clientX - rect.left;
    const mouseY = e.clientY - rect.top;

    // Get zoom direction
    const zoomDirection = e.deltaY < 0 ? 1 : -1;
    const zoomFactor = 1 + zoomDirection * 0.1;

    // Get position before zoom
    const worldPos = {
      x: (mouseX - app.stage.position.x) / app.stage.scale.x,
      y: (mouseY - app.stage.position.y) / app.stage.scale.y,
    };

    // Apply zoom (limit scale between 0.1 and 3.0)
    const newScale = Math.max(
      0.1,
      Math.min(3.0, app.stage.scale.x * zoomFactor)
    );
    app.stage.scale.set(newScale);

    // Adjust position to zoom toward mouse
    app.stage.position.x = mouseX - worldPos.x * newScale;
    app.stage.position.y = mouseY - worldPos.y * newScale;

    // Render the changes
    app.render();
    console.log(`🔍 Zoom: ${newScale.toFixed(2)}`);
  });

  // Pan functionality
  canvas.addEventListener('mousedown', (e) => {
    isDragging = true;
    lastPosition = { x: e.clientX, y: e.clientY };
    canvas.style.cursor = 'grabbing';
  });

  canvas.addEventListener('mousemove', (e) => {
    if (!isDragging) return;

    const dx = e.clientX - lastPosition.x;
    const dy = e.clientY - lastPosition.y;

    app.stage.position.x += dx;
    app.stage.position.y += dy;

    lastPosition = { x: e.clientX, y: e.clientY };

    // Render the changes
    app.render();
  });

  window.addEventListener('mouseup', () => {
    if (isDragging) {
      isDragging = false;
      canvas.style.cursor = 'grab';
    }
  });

  // Set initial cursor
  canvas.style.cursor = 'grab';

  console.log('✅ Mouse events setup complete');
}

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
