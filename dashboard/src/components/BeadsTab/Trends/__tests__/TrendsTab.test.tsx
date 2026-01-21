import { render, screen, fireEvent, cleanup } from '@testing-library/react';
import { TrendsTab } from '../TrendsTab';
import '@testing-library/jest-dom';

class MockResizeObserver {
  callback: ResizeObserverCallback;

  constructor(callback: ResizeObserverCallback) {
    this.callback = callback;
  }

  observe(target: Element): void {
    this.callback(
      [
        {
          target,
          contentRect: new DOMRectReadOnly(0, 0, 200, 200),
          borderBoxSize: [{ blockSize: 200, inlineSize: 200 }],
          contentBoxSize: [{ blockSize: 200, inlineSize: 200 }],
          devicePixelContentBoxSize: [{ blockSize: 200, inlineSize: 200 }],
        },
      ] as ResizeObserverEntry[],
      this as ResizeObserver
    );
  }

  unobserve(): void {}
  disconnect(): void {}
}

(global as any).ResizeObserver = MockResizeObserver;

jest.mock('../HashrateTab', () => ({
  __esModule: true,
  default: () => <div data-testid="hashrate-tab">Hashrate Content</div>,
}));

jest.mock('../LatencyTab', () => ({
  __esModule: true,
  default: () => <div data-testid="latency-tab">Latency Content</div>,
}));

jest.mock('../TransactionsTab', () => ({
  __esModule: true,
  default: (props: any) => (
    <div data-testid="transactions-tab">
      Transactions Content | hovered: {props.chartHovered.toString()}
    </div>
  ),
}));

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
    const hashrateTab = screen.getByTestId('hashrate-tab');
    expect(hashrateTab).toBeInTheDocument();
    expect(hashrateTab.parentElement).toHaveClass('block');
    const latencyTab = screen.getByTestId('latency-tab');
    const transactionsTab = screen.getByTestId('transactions-tab');
    expect(latencyTab.parentElement).toHaveClass('hidden');
    expect(transactionsTab.parentElement).toHaveClass('hidden');
  });

  it('switches to latency tab when clicked', () => {
    render(<TrendsTab timeRange="24h" />);
    const latencyBtn = screen.getByRole('button', { name: /latency/i });
    fireEvent.click(latencyBtn);

    const latencyTab = screen.getByTestId('latency-tab');
    expect(latencyTab).toBeInTheDocument();
    expect(latencyTab.parentElement).toHaveClass('block');

    const hashrateTab = screen.getByTestId('hashrate-tab');
    const transactionsTab = screen.getByTestId('transactions-tab');
    expect(hashrateTab.parentElement).toHaveClass('hidden');
    expect(transactionsTab.parentElement).toHaveClass('hidden');
  });

  it('switches to transactions tab and passes props', () => {
    render(<TrendsTab timeRange="24h" />);
    const txBtn = screen.getByRole('button', { name: /transactions/i });
    fireEvent.click(txBtn);
    const transactionsTab = screen.getByTestId('transactions-tab');
    expect(transactionsTab).toBeInTheDocument();
    expect(transactionsTab.textContent).toContain('hovered: false');
  });

  it('renders all tab buttons correctly', () => {
    render(<TrendsTab timeRange="24h" />);
    expect(
      screen.getByRole('button', { name: /hashrate/i })
    ).toBeInTheDocument();
    expect(
      screen.getByRole('button', { name: /latency/i })
    ).toBeInTheDocument();
    expect(
      screen.getByRole('button', { name: /transactions/i })
    ).toBeInTheDocument();
  });

  it('switches tabs using the mobile dropdown', () => {
    render(<TrendsTab timeRange="24h" />);

    // The dropdown initially displays "Hashrate" (because activeSubTab defaults to 'hashrate')
    const mobileSelect = screen.getByDisplayValue('Hashrate');
    expect(mobileSelect).toBeInTheDocument();

    // Switch to Latency using the dropdown
    fireEvent.change(mobileSelect, { target: { value: 'latency' } });

    // Assert Latency content is now visible
    const latencyTab = screen.getByTestId('latency-tab');
    expect(latencyTab.parentElement).toHaveClass('block');

    // Assert Hashrate content is now hidden
    const hashrateTab = screen.getByTestId('hashrate-tab');
    expect(hashrateTab.parentElement).toHaveClass('hidden');
  });
});
