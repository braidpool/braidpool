import { describe, it, expect } from 'vitest';
import { mapApiToMiner, getAlerts } from '../Utils';
import { Miner } from '../Types';

// helper to build a base miner API response
const baseApiMiner = () => ({
  id: 'miner-1',
  ip: '192.168.1.10',
  hostname: 'rig-01',
  mac: 'AA:BB:CC:DD:EE:FF',
  make: 'Antminer',
  model: 'S19',
  firmware: 'v1.0.0',
  is_online: true,
  is_mining: true,
  uptime: 3600,
  errors: [],
  last_seen: null,
  hashrate_current: 95e12,
  hashrate_avg: 90e12,
  expected_hashrate: 95e12,
  temperature: 70,
  temperature_max: 80,
  vr_temperature: 60,
  power_usage: 3200,
  power_limit: 3500,
  efficiency: 33.6,
  voltage: 12,
  fan_speeds: [5000, 5100],
  chip_count: 76,
  primary_pool: 'stratum+tcp://pool.example.com',
  pools: [],
});

// helper to build a mapped Miner object for getAlerts tests
const baseMiner = (): Miner => mapApiToMiner(baseApiMiner());

// ---- mapApiToMiner ----

describe('mapApiToMiner', () => {
  it('maps a healthy miner to status online', () => {
    const miner = mapApiToMiner(baseApiMiner());
    expect(miner.status).toBe('online');
  });

  it('maps is_online: false to status offline', () => {
    const miner = mapApiToMiner({ ...baseApiMiner(), is_online: false });
    expect(miner.status).toBe('offline');
  });

  it('maps is_mining: false to status warning', () => {
    const miner = mapApiToMiner({ ...baseApiMiner(), is_mining: false });
    expect(miner.status).toBe('warning');
  });

  it('maps is_mining: null to status warning', () => {
    const miner = mapApiToMiner({ ...baseApiMiner(), is_mining: null });
    expect(miner.status).toBe('warning');
  });

  it('maps critical temperature to status warning', () => {
    const miner = mapApiToMiner({ ...baseApiMiner(), temperature: 90 });
    expect(miner.status).toBe('warning');
  });

  it('maps critical vr_temperature to status warning', () => {
    const miner = mapApiToMiner({ ...baseApiMiner(), vr_temperature: 100 });
    expect(miner.status).toBe('warning');
  });

  it('uses Unknown as fallback for missing hostname', () => {
    const miner = mapApiToMiner({ ...baseApiMiner(), hostname: undefined });
    expect(miner.hostname).toBe('Unknown');
  });

  it('uses Unknown as fallback for missing make', () => {
    const miner = mapApiToMiner({ ...baseApiMiner(), make: undefined });
    expect(miner.make).toBe('Unknown');
  });

  it('uses Never as fallback when last_seen is null', () => {
    const miner = mapApiToMiner({ ...baseApiMiner(), last_seen: null });
    expect(miner.lastSeen).toBe('Never');
  });

  it('formats last_seen as a time string when provided', () => {
    const miner = mapApiToMiner({
      ...baseApiMiner(),
      last_seen: '2024-01-01T12:00:00.000Z',
    });
    expect(miner.lastSeen).not.toBe('Never');
  });

  it('defaults errors to empty array when missing', () => {
    const miner = mapApiToMiner({ ...baseApiMiner(), errors: undefined });
    expect(miner.errors).toEqual([]);
  });
});

// ---- getAlerts ----

describe('getAlerts', () => {
  it('returns no alerts for a healthy online miner', () => {
    const alerts = getAlerts(baseMiner());
    expect(alerts).toHaveLength(0);
  });

  it('returns empty array when miner is offline', () => {
    const miner = { ...baseMiner(), status: 'offline' as const };
    const alerts = getAlerts(miner);
    expect(alerts).toHaveLength(0);
  });

  it('returns Not Mining alert when is_mining is false and no other issue', () => {
    const miner = { ...baseMiner(), is_mining: false, temperature: 70 };
    const alerts = getAlerts(miner);
    expect(alerts.some((a) => a.message === 'Not Mining')).toBe(true);
  });

  it('returns ASIC Temp High alert when temperature exceeds threshold', () => {
    const miner = { ...baseMiner(), temperature: 90 };
    const alerts = getAlerts(miner);
    expect(alerts.some((a) => a.message === 'ASIC Temp High')).toBe(true);
  });

  it('returns VR Temp High alert when vr_temperature exceeds threshold', () => {
    const miner = { ...baseMiner(), vr_temperature: 100 };
    const alerts = getAlerts(miner);
    expect(alerts.some((a) => a.message === 'VR Temp High')).toBe(true);
  });

  it('returns Voltage Low alert when voltage is below threshold', () => {
    const miner = { ...baseMiner(), voltage: 3 };
    const alerts = getAlerts(miner);
    expect(alerts.some((a) => a.message === 'Voltage Low')).toBe(true);
  });

  it('returns Fan Speed Low alert when a fan speed is below threshold', () => {
    const miner = { ...baseMiner(), fan_speeds: [5000, 500] };
    const alerts = getAlerts(miner);
    expect(alerts.some((a) => a.message === 'Fan Speed Low')).toBe(true);
  });

  it('can return multiple alerts at once', () => {
    const miner = {
      ...baseMiner(),
      temperature: 90,
      vr_temperature: 100,
      voltage: 3,
    };
    const alerts = getAlerts(miner);
    expect(alerts.length).toBeGreaterThan(1);
  });
});
