import { render, screen } from '@testing-library/react';
import MempoolPanel from '../Mempool';
import { MempoolInfo } from '../Types';

describe('MempoolPanel', () => {
  const mockMempool: MempoolInfo = {
    loaded: true,
    size: 1234,
    bytes: 567890,
    usage: 1048576,
    maxmempool: 2097152,
    mempoolminfee: 0.00001,
    minrelaytxfee: 0.00001,
  };

  it('renders mempool statistics and usage bar', () => {
    render(<MempoolPanel mempool={mockMempool} />);
    expect(screen.getByText(/Mempool Statistics/i)).toBeInTheDocument();
    expect(screen.getByText('1,234')).toBeInTheDocument();
    expect(screen.getByText(/BTC\/kvB/i)).toBeInTheDocument();
    expect(screen.getByText(/Memory Usage/i)).toBeInTheDocument();
  });
});
