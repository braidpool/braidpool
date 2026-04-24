import type { AnimationSpeedOption } from './Types';

// Visual constants
export const NODE_RADIUS = 30;
export const PADDING = 100; // Additional padding for SVG

// Color constants
export const COLORS = [
  `rgba(${217}, ${95}, ${2}, 1)`,
  `rgba(${117}, ${112}, ${179}, 1)`,
  `rgba(${102}, ${166}, ${30}, 1)`,
  `rgba(${231}, ${41}, ${138}, 1)`,
];

// Layout constants (commented out but preserved for reference)
// export const VERTICAL_SPACING = 150;

export const DEFAULT_ANIMATION_SPEED = 'normal';

export const ANIMATION_SPEED_OPTIONS: AnimationSpeedOption[] = [
  { value: 'slow', label: 'Slow', scale: 1.8 },
  { value: 'normal', label: 'Normal', scale: 0.75 },
  { value: 'fast', label: 'Fast', scale: 0.3 },
];

export const DEFAULT_COHORT_ANIMATION_DURATION_MS = 1000;
export const DEFAULT_COHORT_ANIMATION_DELAY_MS = 100;
