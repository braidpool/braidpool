import {
  formatBytes,
  TABS,
  paginate,
  calculateTotalPages,
  useIsSmallScreen,
} from '../Utils';
import { renderHook, act } from '@testing-library/react';

// ---- formatBytes ----
describe('formatBytes', () => {
  it('should format 0 bytes correctly', () => {
    expect(formatBytes(0)).toBe('0 B');
  });

  it('should format bytes to KB, MB, GB correctly', () => {
    expect(formatBytes(1024)).toBe('1 KB');
    expect(formatBytes(1048576)).toBe('1 MB');
    expect(formatBytes(1073741824)).toBe('1 GB');
  });
});

// ---- TABS ----
describe('TABS', () => {
  it('should contain the correct tab labels and values', () => {
    expect(TABS).toEqual([
      { label: 'Blockchain', value: 'blockchain' },
      { label: 'Peers', value: 'peers' },
      { label: 'Network', value: 'bandwidth' },
      { label: 'Mempool', value: 'mempool' },
    ]);
  });
});

// ---- paginate ----
describe('paginate', () => {
  const data = [1, 2, 3, 4, 5, 6];

  it('should paginate correctly', () => {
    expect(paginate(data, 1, 2)).toEqual([1, 2]);
    expect(paginate(data, 2, 2)).toEqual([3, 4]);
    expect(paginate(data, 3, 2)).toEqual([5, 6]);
  });

  it('should return empty array if page exceeds range', () => {
    expect(paginate(data, 4, 2)).toEqual([]);
  });
});

// ---- calculateTotalPages ----
describe('calculateTotalPages', () => {
  it('should calculate total pages correctly', () => {
    expect(calculateTotalPages(10, 3)).toBe(4);
    expect(calculateTotalPages(20, 5)).toBe(4);
    expect(calculateTotalPages(0, 5)).toBe(0);
  });
});

// ---- useIsSmallScreen ----
describe('useIsSmallScreen', () => {
  const originalInnerWidth = global.innerWidth;

  afterEach(() => {
    global.innerWidth = originalInnerWidth;
  });

  it('should return true for small screens', () => {
    global.innerWidth = 500;
    const { result } = renderHook(() => useIsSmallScreen(640));
    expect(result.current).toBe(true);
  });

  it('should return false for large screens', () => {
    global.innerWidth = 800;
    const { result } = renderHook(() => useIsSmallScreen(640));
    expect(result.current).toBe(false);
  });
});
