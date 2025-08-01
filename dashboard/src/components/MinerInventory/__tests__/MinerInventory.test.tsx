import { render, screen, fireEvent, waitFor } from '@testing-library/react';
import MinerInventoryDashboard from '../MinerInventoryDashboard';
describe('MinerInventoryDashboard', () => {
  const mockMinerData = {
    macAddr: 'abc123',
    hostname: 'MockMiner1',
    hashRate: 100,
    power: 500,
    uptimeSeconds: 3600,
    temp: 75,
    overheat_mode: false,
    frequency: 800,
    fanspeed: 2000,
    bestDiff: 123456,
    ASICModel: 'BitAxe Pro',
  };

  beforeEach(() => {
    global.fetch = jest.fn().mockResolvedValue({
      ok: true,
      json: async () => mockMinerData,
    });
  });

  afterEach(() => {
    jest.clearAllMocks();
  });

  it('renders loading state initially', async () => {
    render(<MinerInventoryDashboard />);
    expect(screen.getByText(/Loading the Miner Data/i)).toBeInTheDocument();
    await waitFor(() => {
      expect(
        screen.queryByText(/Loading the Miner Data/i)
      ).not.toBeInTheDocument();
    });
  });

  it('renders miner info after successful fetch', async () => {
    render(<MinerInventoryDashboard />);
    await waitFor(() => {
      expect(screen.getByText(/MockMiner1/)).toBeInTheDocument();
      expect(screen.getByText(/Hashrate: 100.00 GH\/s/)).toBeInTheDocument();
      expect(screen.getByText(/ASICModel:BitAxe Pro/)).toBeInTheDocument();
    });
  });

  it('displays error message on fetch failure', async () => {
    (fetch as jest.Mock).mockResolvedValueOnce({ ok: false });
    render(<MinerInventoryDashboard />);
    await waitFor(() => {
      expect(screen.getByText(/Error:/)).toBeInTheDocument();
    });
  });

  it('adds a new miner by IP', async () => {
    render(<MinerInventoryDashboard />);

    await waitFor(() =>
      expect(
        screen.queryByPlaceholderText(/Enter miner IP/i)
      ).toBeInTheDocument()
    );

    const input = screen.getByPlaceholderText(/Enter miner IP/i);
    fireEvent.change(input, { target: { value: '192.168.1.100' } });

    const button = screen.getByText(/Add Miner/i);
    fireEvent.click(button);

    await waitFor(() =>
      expect(screen.getAllByText(/MockMiner1/i).length).toBeGreaterThan(1)
    );
  });

  it('clears all miners when clear button is clicked', async () => {
    render(<MinerInventoryDashboard />);

    await waitFor(() => {
      expect(screen.getByText(/MockMiner1/)).toBeInTheDocument();
    });

    const clearButton = screen.getByText(/Clear Miners/i);
    fireEvent.click(clearButton);

    await waitFor(() => {
      expect(screen.getByText(/No mining devices found/i)).toBeInTheDocument();
    });
  });
});
