import { render, screen, fireEvent, cleanup } from '@testing-library/react';
import { TrendsTab } from '../TrendsTab';
import '@testing-library/jest-dom';

jest.mock('../HashrateTab', () => () => (
  <div data-testid="hashrate-tab">Hashrate Content</div>
));
jest.mock('../LatencyTab', () => () => (
  <div data-testid="latency-tab">Latency Content</div>
));
jest.mock('../TransactionsTab', () => (props: any) => (
  <div data-testid="transactions-tab">
    Transactions Content | hovered: {props.chartHovered.toString()}
  </div>
));

// Mock TrendsTABS
jest.mock('../../lib/Constants', () => ({
  TrendsTABS: [
    { id: 'hashrate', label: 'Hashrate', icon: () => <span>Hashrate</span> },
    { id: 'latency', label: 'Latency', icon: () => <span>Latency</span> },
    {
      id: 'transactions',
      label: 'Transactions',
      icon: () => <span>Transactions</span>,
    },
  ],
}));

describe('<TrendsTab />', () => {
  afterEach(() => {
    cleanup();
    jest.clearAllMocks();
  });

  it('renders the initial hashrate tab by default', () => {
    render(<TrendsTab timeRange="24h" />);

    expect(screen.getByText(/Hashrate Content/i)).toBeInTheDocument();
    expect(screen.queryByTestId('latency-tab')).not.toBeInTheDocument();
    expect(screen.queryByTestId('transactions-tab')).not.toBeInTheDocument();
  });

  it('switches to latency tab when clicked', () => {
    render(<TrendsTab timeRange="24h" />);

    fireEvent.click(screen.getByText('Latency'));
    expect(screen.getByTestId('latency-tab')).toBeInTheDocument();
    expect(screen.queryByTestId('hashrate-tab')).not.toBeInTheDocument();
    expect(screen.queryByTestId('transactions-tab')).not.toBeInTheDocument();
  });

  it('switches to transactions tab and passes props', () => {
    render(<TrendsTab timeRange="24h" />);

    fireEvent.click(screen.getByText('Transactions'));

    const transactionsTab = screen.getByTestId('transactions-tab');
    expect(transactionsTab).toBeInTheDocument();
    expect(transactionsTab.textContent).toContain('hovered: false');
  });

  it('renders all tab buttons correctly', () => {
    render(<TrendsTab timeRange="24h" />);
    expect(screen.getByText('Hashrate')).toBeInTheDocument();
    expect(screen.getByText('Latency')).toBeInTheDocument();
    expect(screen.getByText('Transactions')).toBeInTheDocument();
  });
});
