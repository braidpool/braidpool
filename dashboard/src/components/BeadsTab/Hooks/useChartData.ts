import { useState, useEffect } from 'react';
import { TIME_RANGES } from '../lib/constants';
import type { ChartDataPoint } from '../lib/types';
export function useChartData(timeRange: string) {
  const [data, setData] = useState<ChartDataPoint[]>([]);
  const [isLoading, setIsLoading] = useState(true);
  const [dateRange, setDateRange] = useState({ start: '', end: '' });

  // Generate chart data based on time range
  useEffect(() => {
    setIsLoading(true);

    // Find the selected time range
    const selectedRange =
      TIME_RANGES.find((range) => range.value === timeRange) || TIME_RANGES[1]; // Default to month

    // Generate dates for the selected range
    const endDate = new Date();
    const startDate = new Date();
    startDate.setDate(endDate.getDate() - selectedRange.days);

    // Set date range for display
    setDateRange({
      start: startDate.toLocaleDateString('en-US', {
        year: 'numeric',
        month: 'short',
        day: 'numeric',
      }),
      end: endDate.toLocaleDateString('en-US', {
        year: 'numeric',
        month: 'short',
        day: 'numeric',
      }),
    });

    // Determine interval based on range
    let interval = 1; // days
    let format = 'day';

    if (timeRange === 'week') {
      interval = 1;
      format = 'day';
    } else if (timeRange === 'month') {
      interval = 3;
      format = 'day';
    } else if (timeRange === 'quarter') {
      interval = 7;
      format = 'week';
    } else if (timeRange === 'year') {
      interval = 30;
      format = 'month';
    }

    // Generate data points
    const dataPoints: ChartDataPoint[] = [];
    const currentDate = new Date(startDate);

    while (currentDate <= endDate) {
      const value = Math.floor(Math.random() * 100) + 50;

      // Improved date formatting
      let label = '';
      if (format === 'day') {
        label = currentDate.toLocaleDateString('en-US', {
          month: 'short',
          day: 'numeric',
        });
      } else if (format === 'week') {
        const weekNumber = Math.ceil(
          (currentDate.getDate() -
            1 +
            new Date(
              currentDate.getFullYear(),
              currentDate.getMonth(),
              1
            ).getDay()) /
            7
        );
        label = `${currentDate.toLocaleDateString('en-US', { month: 'short', day: 'numeric' })}`;
      } else if (format === 'month') {
        label = currentDate.toLocaleDateString('en-US', {
          month: 'short',
          year: '2-digit',
        });
      }

      // Add data point with full date information
      dataPoints.push({
        value,
        label,
        date: new Date(currentDate),
        formattedDate: currentDate.toLocaleDateString('en-US', {
          year: 'numeric',
          month: 'short',
          day: 'numeric',
          weekday: 'short',
        }),
        trend:
          dataPoints.length > 0
            ? value > dataPoints[dataPoints.length - 1].value
              ? 'up'
              : 'down'
            : 'neutral',
      });

      // Increment date
      currentDate.setDate(currentDate.getDate() + interval);
    }

    // Simulate API delay
    setTimeout(() => {
      setData(dataPoints);
      setIsLoading(false);
    }, 500);
  }, [timeRange]);

  return { data, isLoading, dateRange };
}
