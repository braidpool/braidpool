export const formatBytes = (bytes: number) => {
  const sizes = ['B', 'KB', 'MB', 'GB', 'TB'];
  if (bytes === 0) return '0 B';
  const i = Math.floor(Math.log(bytes) / Math.log(1024));
  return Math.round((bytes / Math.pow(1024, i)) * 100) / 100 + ' ' + sizes[i];
};
export const TABS = [
  { label: 'Blockchain', value: 'blockchain' },
  { label: 'Peers', value: 'peers' },
  { label: 'Network', value: 'bandwidth' },
  { label: 'Mempool', value: 'mempool' },
];
