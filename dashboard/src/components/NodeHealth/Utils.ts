export function formatBytes(bytes: number): string {
  if (bytes === 0) return '0 B';
  const k = 1024;
  const sizes = ['B', 'KB', 'MB', 'GB', 'TB'];
  const i = Math.floor(Math.log(bytes) / Math.log(k));
  return parseFloat((bytes / Math.pow(k, i)).toFixed(2)) + ' ' + sizes[i];
}

export const TABS = [
  { label: 'Blockchain', value: 'blockchain' },
  { label: 'Peers', value: 'peers' },
  { label: 'Network', value: 'bandwidth' },
  { label: 'Mempool', value: 'mempool' },
];
