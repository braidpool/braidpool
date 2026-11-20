export const HISTORY_POINTS = 20;
export const THRESHOLDS = {
  ASIC_TEMP_CRITICAL: 85,
  VR_TEMP_CRITICAL: 95,
  VOLTAGE_LOW: 4,
  FAN_SPEED_LOW: 1000,
} as const;
export const REFRESH_INTERVAL = 1;
// Decimal places for the network hashrate (EH/s) tooltip value.
export const NETWORK_HASHRATE_DECIMALS = 2;
