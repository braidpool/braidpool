import { KILOBYTE } from './Constants';

export function formatBytes(bytes: number): string {
  if (bytes === 0) return '0 B';
  const k = KILOBYTE;
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
export function paginate<T>(
  data: T[],
  currentPage: number,
  itemsPerPage: number
): T[] {
  const startIndex = (currentPage - 1) * itemsPerPage;
  return data.slice(startIndex, startIndex + itemsPerPage);
}
export function calculateTotalPages(
  totalItems: number,
  itemsPerPage: number
): number {
  return Math.ceil(totalItems / itemsPerPage);
}
import { useEffect, useState } from 'react';

export function useIsSmallScreen(breakpoint = 640) {
  const [isSmallScreen, setIsSmallScreen] = useState(false);

  useEffect(() => {
    const checkSize = () => setIsSmallScreen(window.innerWidth < breakpoint);
    checkSize();
    window.addEventListener('resize', checkSize);
    return () => window.removeEventListener('resize', checkSize);
  }, [breakpoint]);

  return isSmallScreen;
}
