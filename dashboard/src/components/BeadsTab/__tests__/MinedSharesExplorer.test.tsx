import { render, screen, waitFor, fireEvent } from '@testing-library/react';
import MinedSharesExplorer from '../MinedSharesExplorer';
import '@testing-library/jest-dom';

jest.mock('../DashboardHeader', () => {
  return function MockDashboardHeader({ setActiveTab }: any) {
    return (
      <div>
        <div>DashboardHeader</div>
        <button onClick={() => setActiveTab('beads')}>Beads Tab</button>
        <button onClick={() => setActiveTab('trends')}>Trends Tab</button>
        <button onClick={() => setActiveTab('rewards')}>Rewards Tab</button>
        <button onClick={() => setActiveTab('pool')}>Pool Tab</button>
      </div>
    );
  };
});

jest.mock('../../BraidPoolDAG/BraidPoolDAG', () => {
  return function MockGraphVisualization() {
    return <div data-testid="graph-visualization">GraphVisualization</div>;
  };
});

jest.mock('../Trends/TrendsTab', () => {
  const MockTrendsTab = function MockTrendsTab() {
    return <div>TrendsTab</div>;
  };

  return {
    TrendsTab: MockTrendsTab,
    __esModule: true,
    default: MockTrendsTab,
  };
});

jest.mock('../Reward/RewardsDashboard', () => {
  return {
    RewardsDashboard: function MockRewardsDashboard() {
      return <div>RewardsDashboard</div>;
    },
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

  it('renders the component with initial state', () => {
    render(<MinedSharesExplorer />);

    expect(screen.getByText('DashboardHeader')).toBeInTheDocument();
    expect(screen.getByTestId('graph-visualization')).toBeInTheDocument();
  });

  it('shows GraphVisualization by default on beads tab', () => {
    render(<MinedSharesExplorer />);

    expect(screen.getByTestId('graph-visualization')).toBeInTheDocument();
  });

  it('switches to trends tab when activeTab changes', async () => {
    render(<MinedSharesExplorer />);

    const trendsButton = screen.getByText('Trends Tab');
    fireEvent.click(trendsButton);

    await waitFor(() => {
      expect(screen.getByText('TrendsTab')).toBeInTheDocument();
    });
  });

  it('switches to rewards tab when activeTab changes', async () => {
    render(<MinedSharesExplorer />);

    const rewardsButton = screen.getByText('Rewards Tab');
    fireEvent.click(rewardsButton);

    await waitFor(() => {
      expect(screen.getByText('RewardsDashboard')).toBeInTheDocument();
    });
  });

  it('switches to pool tab when activeTab changes', async () => {
    render(<MinedSharesExplorer />);

    const poolButton = screen.getByText('Pool Tab');
    fireEvent.click(poolButton);

    await waitFor(() => {
      expect(screen.getByText('PoolDominance')).toBeInTheDocument();
    });
  });

  it('switches back to beads tab', async () => {
    render(<MinedSharesExplorer />);

    // Go to trends first
    fireEvent.click(screen.getByText('Trends Tab'));
    await waitFor(() => {
      expect(screen.getByText('TrendsTab')).toBeInTheDocument();
    });

    // Go back to beads
    fireEvent.click(screen.getByText('Beads Tab'));
    await waitFor(() => {
      expect(screen.getByTestId('graph-visualization')).toBeInTheDocument();
    });
  });
});
