import { render, screen, fireEvent } from '@testing-library/react';
import Peers from '../Peers';
import { PeerInfo } from '../Types';

const mockPeers: PeerInfo[] = Array.from({ length: 12 }).map((_, i) => ({
  id: i,
  addr: `192.168.0.${i}`,
  version: 70015,
  subver: '/Satoshi:0.21.0/',
  inbound: i % 2 === 0,
  startingheight: 100,
  synced_headers: 100,
  synced_blocks: 100,
  pingtime: 30 + i,
  bytessent: 1048576 * (i + 1),
  bytesrecv: 524288 * (i + 1),
}));

describe('Peers Component', () => {
  test('renders peers and pagination', () => {
    render(<Peers peers={mockPeers} />);

    expect(screen.getByText(/Connected Peers/i)).toBeInTheDocument();

    // Check if 10 peers are shown on first page
    const peerAddresses = screen.getAllByText(/192.168.0./i);
    expect(peerAddresses).toHaveLength(10);

    // Pagination shows current page info
    expect(screen.getByText(/Page 1 of 2/i)).toBeInTheDocument();
  });

  test('pagination works', () => {
    render(<Peers peers={mockPeers} />);

    fireEvent.click(screen.getByText(/Next/i));
    expect(screen.getByText(/Page 2 of 2/i)).toBeInTheDocument();

    fireEvent.click(screen.getByText(/Previous/i));
    expect(screen.getByText(/Page 1 of 2/i)).toBeInTheDocument();
  });

  test('shows correct inbound/outbound labels', () => {
    render(<Peers peers={mockPeers} />);

    expect(screen.getAllByText(/Inbound/i).length).toBeGreaterThan(0);
    expect(screen.getAllByText(/Outbound/i).length).toBeGreaterThan(0);
  });
});
