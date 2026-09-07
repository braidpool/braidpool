import { Miner, MinerAlert as Alert } from './Types';
import { THRESHOLDS } from './Constant';
const determineStatus = (data: any): 'online' | 'warning' | 'offline' => {
  // Truly offline device not responding on the network
  if (!data.is_online) return 'offline';
  // Online but not mining = thermal protection(overheat mode), error stop, or initialising
  if (data.is_mining === false || data.is_mining == null) return 'warning';

  if (
    (data.temperature || 0) > THRESHOLDS.ASIC_TEMP_CRITICAL ||
    (data.vr_temperature || 0) > THRESHOLDS.VR_TEMP_CRITICAL ||
    (data.errors?.length || 0) > 0
  )
    return 'warning';
  return 'online';
};

export const mapApiToMiner = (m: any, lastSeenFallback = 'Never'): Miner => ({
  id: m.id,
  ip: m.ip,
  hostname: m.hostname || 'Unknown',
  mac: m.mac || 'Unknown',
  make: m.make || 'Unknown',
  model: m.model || 'Unknown',
  firmware: m.firmware || 'Unknown',
  status: determineStatus(m),
  is_mining: m.is_mining || false,
  uptime: m.uptime || 0,
  errors: m.errors || [],
  alerts: 0,
  lastSeen: m.last_seen
    ? new Date(m.last_seen).toLocaleTimeString()
    : lastSeenFallback,
  hashrate_current: m.hashrate_current || 0,
  hashrate_avg: m.hashrate_avg || 0,
  expected_hashrate: m.expected_hashrate || 0,
  temperature: m.temperature || 0,
  temperature_max: m.temperature_max || 0,
  vr_temperature: m.vr_temperature || 0,
  power_usage: m.power_usage || 0,
  power_limit: m.power_limit || 0,
  efficiency: m.efficiency || 0,
  voltage: m.voltage || 0,
  fan_speeds: m.fan_speeds || [],
  chip_count: m.chip_count || 0,
  primary_pool: m.primary_pool || 'No Pool',
  pools: m.pools || [],
});

//alerts from the device
export const getAlerts = (miner: Miner): Alert[] => {
  if (miner.status === 'offline') return [];
  const alerts: Alert[] = [];
  if (!miner.is_mining) {
    const temp = miner.temperature || 0;
    if (temp > 0 && temp >= THRESHOLDS.ASIC_TEMP_CRITICAL - 10) {
      alerts.push({ message: `Overheat Mode (${temp}\u00B0C)` });
    } else if (miner.errors && miner.errors.length > 0) {
      alerts.push({ message: 'Stopped — device error' });
    } else {
      alerts.push({ message: 'Not Mining' });
    }
  }
  if (miner.temperature > THRESHOLDS.ASIC_TEMP_CRITICAL) {
    alerts.push({ message: `ASIC Temp High` });
  }
  if (miner.vr_temperature > THRESHOLDS.VR_TEMP_CRITICAL) {
    alerts.push({ message: `VR Temp High` });
  }
  if (miner.voltage && miner.voltage < THRESHOLDS.VOLTAGE_LOW) {
    alerts.push({ message: `Voltage Low` });
  }
  if (
    miner.fan_speeds !== undefined &&
    miner.fan_speeds.some((s) => s < THRESHOLDS.FAN_SPEED_LOW)
  ) {
    alerts.push({ message: `Fan Speed Low` });
  }
  return alerts;
};
