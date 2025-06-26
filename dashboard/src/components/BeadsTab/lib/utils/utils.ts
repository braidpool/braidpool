
export function shortenHash(hash: string, start = 6, end = 6): string {
  if (hash.length <= start + end) return hash;
  return `${hash.slice(0, start)}...${hash.slice(-end)}`;
}

export function formatWork(difficulty: number): {
  value: string;
  unit: string;
} {
  const units = ['GH', 'TH', 'PH', 'EH'];
  let work = difficulty / 1e9;
  let i = 0;
  while (work >= 1000 && i < units.length - 1) {
    work /= 1000;
    i++;
  }
  return {
    value: work >= 1e21 ? work.toExponential(4) : work.toFixed(2),
    unit: units[i],
  };
}

export function formatBlockLabel(height: number): string {
  return `Block ${height.toLocaleString()}`;
}
