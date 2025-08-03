import { render, screen, fireEvent, act } from '@testing-library/react';
import BeadRow from '../BeadRow';
import { Bead, Transaction } from '../lib/Types';

const mockBead: Bead = {
  id: 'abc123',
  name: 'Bead A',
  timestamp: '2025-07-08 10:30:00',
  difficulty: 12345678,
  transactions: 2,
  reward: 0.02,
  parents: ['parenthash1', 'parenthash2'],
};

const mockTransactions: Transaction[] = [
  {
    id: 'tx1',
    hash: 'abc123hash',
    timestamp: '2025-07-08T10:29:00Z',
    count: 1,
    blockId: 'block1',
    fee: 0.01,
    size: 200,
    feePaid: '0.01',
    feeRate: 50,
    inputs: 1,
    outputs: 2,
  },
];

beforeAll(() => {
  Object.assign(navigator, {
    clipboard: {
      writeText: jest.fn().mockResolvedValue(undefined),
    },
  });
});

describe('<BeadRow />', () => {
  const onToggleMock = jest.fn();

  beforeEach(() => {
    jest.clearAllMocks();
  });

  it('renders bead details correctly', () => {
    render(
      <BeadRow
        bead={mockBead}
        isExpanded={false}
        onToggle={onToggleMock}
        transactions={mockTransactions}
        isActive={false}
      />
    );

    expect(screen.getByText('Bead A')).toBeInTheDocument();
    expect(screen.getByText('2025-07-08 10:30:00')).toBeInTheDocument();
    expect(screen.getByText(/mBTC/)).toBeInTheDocument();
    expect(screen.getByText('2')).toBeInTheDocument(); // transaction count
  });

  it('calls onToggle when row is clicked', () => {
    render(
      <BeadRow
        bead={mockBead}
        isExpanded={false}
        onToggle={onToggleMock}
        transactions={mockTransactions}
        isActive={false}
      />
    );
    const buttons = screen.getAllByRole('button');
    fireEvent.click(buttons[0]);
    expect(onToggleMock).toHaveBeenCalledWith(mockBead.id);
  });

  it('toggles reward tooltip on click without toggling parent', () => {
    render(
      <BeadRow
        bead={mockBead}
        isExpanded={false}
        onToggle={onToggleMock}
        transactions={mockTransactions}
        isActive={false}
      />
    );

    const rewardEl = screen.getByText(/mBTC/);
    fireEvent.click(rewardEl);

    expect(screen.getAllByText(/mBTC/).length).toBeGreaterThan(1); // tooltip visible
    expect(onToggleMock).not.toHaveBeenCalled(); // no parent toggle
  });

  it('shows "Copied!" when parent hash is clicked', async () => {
    render(
      <BeadRow
        bead={mockBead}
        isExpanded={false}
        onToggle={onToggleMock}
        transactions={mockTransactions}
        isActive={false}
      />
    );

    const parentBtn = screen.getByText(/parenthash1/i);
    await act(async () => {
      fireEvent.click(parentBtn);
    });
    expect(await screen.findByText('Copied!')).toBeInTheDocument();
  });

  it('renders transaction list when expanded', () => {
    render(
      <BeadRow
        bead={mockBead}
        isExpanded={true}
        onToggle={onToggleMock}
        transactions={mockTransactions}
        isActive={false}
      />
    );

    expect(screen.getByText(/abc123hash/)).toBeInTheDocument(); // transaction hash
  });

  it('handles keyboard interaction for toggle', () => {
    render(
      <BeadRow
        bead={mockBead}
        isExpanded={false}
        onToggle={onToggleMock}
        transactions={mockTransactions}
        isActive={false}
      />
    );

    const buttons = screen.getAllByRole('button');
    fireEvent.keyDown(buttons[0], { key: 'Enter' });
    expect(onToggleMock).toHaveBeenCalledWith(mockBead.id);
    fireEvent.keyDown(buttons[0], { key: ' ' });
    expect(onToggleMock).toHaveBeenCalledTimes(2);
  });

  it('does not crash with empty parents or transactions', () => {
    const beadWithoutExtras = { ...mockBead, parents: [], transactions: 0 };

    render(
      <BeadRow
        bead={beadWithoutExtras}
        isExpanded={false}
        onToggle={onToggleMock}
        transactions={[]}
        isActive={false}
      />
    );

    expect(screen.queryByText('Parents:')).not.toBeInTheDocument();
  });
});
