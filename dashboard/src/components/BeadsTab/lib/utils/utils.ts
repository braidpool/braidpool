import dayjs from 'dayjs';
export function shortenHash(hash: string, start = 6, end = 6): string {
  if (hash.length <= start + end) return hash;
  return `${hash.slice(0, start)}...${hash.slice(-end)}`;
}
export const TIME_RANGES = [
  {
    value: 'week',
    label: `${dayjs().subtract(6, 'day').format('MMM D')} - ${dayjs().format('MMM D')}`,
  },
  {
    value: 'month',
    label: `${dayjs().subtract(29, 'day').format('MMM D')} - ${dayjs().format('MMM D')}`,
  },
  {
    value: 'quarter',
    label: `${dayjs().subtract(89, 'day').format('MMM D')} - ${dayjs().format('MMM D')}`,
  },
  {
    value: 'year',
    label: `${dayjs().subtract(364, 'day').format('MMM D, YYYY')} - ${dayjs().format('MMM D, YYYY')}`,
  },
];
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

/**
 * Formats a date or date string for chart labels
 * @param date - Date object, ISO string, or any date-like value
 * @returns Formatted time string
 */
export function formatChartTime(date: Date | string | any): string {
  try {
    // If it's already a formatted string that doesn't look like a date, return as is
    if (typeof date === 'string') {
      // If it starts with "Block", it's a block number
      if (date.startsWith('Block')) {
        return date;
      }
      // If it's already a formatted time string (contains : but not -), return as is
      if (date.includes(':') && !date.includes('-')) {
        return date;
      }
      // If it's a simple string that doesn't look like a date, return as is
      if (!date.includes('-') && !date.includes('/') && !date.includes('T')) {
        return date;
      }
    }
    
    let parsedDate: Date;
    
    if (date instanceof Date) {
      parsedDate = date;
    } else if (typeof date === 'string') {
      parsedDate = new Date(date);
    } else {
      parsedDate = new Date();
    }
    
    if (isNaN(parsedDate.getTime())) {
      return 'Invalid Date';
    }
    
    return parsedDate.toLocaleTimeString('en-US', { 
      hour: '2-digit', 
      minute: '2-digit', 
      second: '2-digit',
      hour12: true 
    });
  } catch {
    return 'Invalid Date';
  }
}


export function formatBlockLabel(height: number): string {
  return `Block ${height.toLocaleString()}`;
}
