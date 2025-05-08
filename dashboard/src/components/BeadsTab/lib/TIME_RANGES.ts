import dayjs from 'dayjs';

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
