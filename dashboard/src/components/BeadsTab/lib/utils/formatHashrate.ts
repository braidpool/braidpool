export function formatHashrate(hashrate: number): string {
  const units = ['H/s', 'kH/s', 'MH/s', 'GH/s', 'TH/s', 'PH/s', 'EH/s'];
  let index = 0;
  while (hashrate >= 1000 && index < units.length - 1) {
    hashrate /= 1000;
    index++;
  }
  return `${hashrate.toFixed(2)} ${units[index]}`;
}
