// Pagination constants
export const ITEMS_PER_PAGE = 5;

// WebSocket connection constants
export const MAX_RECONNECT_ATTEMPTS = 5;

// Utility constants
export const KILOBYTE = 1024;
export const TIME_RANGES = [
  { label: '1m', seconds: 60 },
  { label: '5m', seconds: 300 },
  { label: '15m', seconds: 900 },
  { label: '1h', seconds: 3600 },
  { label: '1d', seconds: 86400 },
] as const;
