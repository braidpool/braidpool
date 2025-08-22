/**
 * This file contains all localhost URLs used throughout the application.
 * URLs are organized by service type and include descriptive comments.
 */

// WebSocket URLs for real-time data
export const WEBSOCKET_URLS = {
  // Main WebSocket for general real-time updates (used in multiple components)
  MAIN_WEBSOCKET: 'ws://localhost:5000',

  // WebSocket for BraidPool DAG visualization (simulator API)
  BRAIDPOOL_DAG_WEBSOCKET: 'ws://localhost:65433/',

  // WebSocket for block viewer updates (mempool)
  BLOCK_VIEWER_WEBSOCKET: 'http://localhost:8080/api/v1/ws',
} as const;

// HTTP API URLs for data fetching
export const API_URLS = {
  // API endpoints (mempool api backend for now)
  BRAIDPOOL_API_BASE: 'http://localhost:8999/api/v1',

  // Bitcoin mempool API endpoints (blockstream)
  MEMPOOL_API_BASE: 'http://localhost:3002',
  // Miner Device Api endpoints
  MINER_DEVICE_URL: 'http://localhost:5001',
} as const;

// Specific API endpoint functions for better type safety
export const getBraidPoolBlockUrl = (hash: string): string =>
  `${API_URLS.BRAIDPOOL_API_BASE}/block/${hash}`;

export const getBraidPoolBlocksUrl = (): string =>
  `${API_URLS.BRAIDPOOL_API_BASE}/blocks`;

export const getBraidPoolReplacementsUrl = (): string =>
  `${API_URLS.BRAIDPOOL_API_BASE}/replacements`;

export const getMempoolRecentUrl = (): string =>
  `${API_URLS.MEMPOOL_API_BASE}/mempool/recent`;

export const getMempoolTransactionUrl = (txid: string): string =>
  `${API_URLS.MEMPOOL_API_BASE}/tx/${txid}`;
