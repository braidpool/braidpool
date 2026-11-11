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

(globalThis as any).ResizeObserver = MockResizeObserver;

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

  it('renders the latency tab by default', () => {
    render(<TrendsTab timeRange="24h" />);
    const latencyTab = screen.getByTestId('latency-tab');
    expect(latencyTab.parentElement).toHaveStyle('display: block');
    const transactionsTab = screen.getByTestId('transactions-tab');
    expect(transactionsTab.parentElement).toHaveStyle('display: none');
  });

  it('switches to transactions tab and passes props', () => {
    render(<TrendsTab timeRange="24h" />);
    const txBtn = screen.getByRole('button', { name: /transactions/i });
    fireEvent.click(txBtn);
    const transactionsTab = screen.getByTestId('transactions-tab');
    expect(transactionsTab.parentElement).toHaveStyle('display: block');
    expect(transactionsTab.textContent).toContain('hovered: false');
  });

  it('switches back to latency tab when clicked', () => {
    render(<TrendsTab timeRange="24h" />);
    fireEvent.click(screen.getByRole('button', { name: /transactions/i }));
    fireEvent.click(screen.getByRole('button', { name: /latency/i }));

    expect(screen.getByTestId('latency-tab').parentElement).toHaveStyle(
      'display: block'
    );
    expect(screen.getByTestId('transactions-tab').parentElement).toHaveStyle(
      'display: none'
    );
  });

  it('renders the remaining tab buttons and no hashrate tab', () => {
    render(<TrendsTab timeRange="24h" />);
    expect(
      screen.getByRole('button', { name: /latency/i })
    ).toBeInTheDocument();
    expect(
      screen.getByRole('button', { name: /transactions/i })
    ).toBeInTheDocument();
    expect(
      screen.queryByRole('button', { name: /hashrate/i })
    ).not.toBeInTheDocument();
  });
});
