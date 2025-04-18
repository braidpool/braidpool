/**
 * Formats a number with a specified number of decimal places
 */
export const formatNumber = (value: number | string, decimals = 2): string => {
  const num = typeof value === "string" ? parseFloat(value) : value;
  return isNaN(num) ? "0" : num.toFixed(decimals);
};

/**
 * Formats a number with a unit (PH/s, bps, etc.)
 */
export const formatWithUnit = (
  value: number | string,
  unit: string,
  decimals = 2,
): string => {
  return `${formatNumber(value, decimals)} ${unit}`;
};

/**
 * Formats a timestamp to a human-readable time string
 */
export const formatTime = (date: Date): string => {
  return date.toLocaleTimeString([], {
    hour: "2-digit",
    minute: "2-digit",
    second: "2-digit",
  });
};

/**
 * Formats a date to a human-readable date string
 */
export const formatDate = (date: Date): string => {
  return date.toLocaleDateString([], {
    year: "numeric",
    month: "short",
    day: "numeric",
  });
};

/**
 * Formats a percentage value with a + or - sign
 */
export const formatPercentage = (value: number): string => {
  const sign = value > 0 ? "+" : "";
  return `${sign}${formatNumber(value * 100)}%`;
};

/**
 * Formats a dollar amount
 */
export const formatCurrency = (value: number | string): string => {
  const num = typeof value === "string" ? parseFloat(value) : value;
  return isNaN(num)
    ? "$0.00"
    : new Intl.NumberFormat("en-US", {
        style: "currency",
        currency: "USD",
      }).format(num);
};
