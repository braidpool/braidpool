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
