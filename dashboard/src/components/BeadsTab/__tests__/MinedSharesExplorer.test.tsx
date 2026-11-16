import { render, screen, waitFor, fireEvent } from '@testing-library/react';
import MinedSharesExplorer from '../MinedSharesExplorer';
import '@testing-library/jest-dom';

jest.mock('../DashboardHeader', () => {
  return function MockDashboardHeader({ setActiveTab }: any) {
    return (
      <div>
        <div>DashboardHeader</div>
        <button onClick={() => setActiveTab('pool')}>Pool Tab</button>
      </div>
    );
  };
});

jest.mock('../PoolDominance/PoolDominance', () => {
  return {
    PoolDominance: function MockPoolDominance() {
      return <div>PoolDominance</div>;
    },
  };
});

describe('MinedSharesExplorer', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('renders the header and defaults to the pool dominance tab', () => {
    render(<MinedSharesExplorer />);

    expect(screen.getByText('DashboardHeader')).toBeInTheDocument();
    expect(screen.getByText('PoolDominance')).toBeInTheDocument();
  });

  it('shows PoolDominance when the pool tab is selected', async () => {
    render(<MinedSharesExplorer />);

    fireEvent.click(screen.getByText('Pool Tab'));

    await waitFor(() => {
      expect(screen.getByText('PoolDominance')).toBeInTheDocument();
    });
  });
});
