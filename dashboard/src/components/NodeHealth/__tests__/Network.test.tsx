import { render, screen } from '@testing-library/react';
import NetworkPanel from '../Network';
import { NetworkInfo } from '../Types';

describe('NetworkPanel', () => {
  const mockNetwork: NetworkInfo = {
    version: 1,
    subversion: '/Satoshi:0.21.0/',
    protocolversion: 70015,
    localservices: '',
    localrelay: true,
    timeoffset: 0,
    networkactive: true,
    connections: 8,
    connections_in: 4,
    connections_out: 4,
    relayfee: 0.00001,
    incrementalfee: 0.00001,
    localaddresses: [],
    warnings: '',
  };

  it('renders network status and details', () => {
    render(<NetworkPanel network={mockNetwork} />);
    expect(screen.getByText(/Network Status/i)).toBeInTheDocument();
    expect(screen.getAllByText(/Active/i).length).toBeGreaterThan(0);

    expect(screen.getByText(/Protocol Version/i)).toBeInTheDocument();
    expect(screen.getByText(/Relay Fee/i)).toBeInTheDocument();
    expect(screen.getByText('/Satoshi:0.21.0/')).toBeInTheDocument();
    expect(screen.getByText('70015')).toBeInTheDocument();
    expect(screen.getByText('0.00001 BTC')).toBeInTheDocument();
  });
});
