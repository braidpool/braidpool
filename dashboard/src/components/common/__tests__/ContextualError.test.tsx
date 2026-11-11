import '@testing-library/jest-dom';
import { render, screen, fireEvent, waitFor } from '@testing-library/react';
import ContextualError from '../ContextualError';

describe('ContextualError', () => {
  const mockWriteText = jest.fn();

  beforeEach(() => {
    jest.clearAllMocks();
    Object.assign(navigator, {
      clipboard: {
        writeText: mockWriteText,
      },
    });
  });

  it('renders error message without More info button when details are omitted', () => {
    render(<ContextualError message="WebSocket connection failed" />);

    expect(screen.getByText('WebSocket connection failed')).toBeInTheDocument();
    expect(screen.queryByText('More info')).not.toBeInTheDocument();
  });

  it('toggles technical details panel when More info is clicked', () => {
    render(
      <ContextualError
        message="Connection error"
        details={{ code: 500, endpoint: 'ws://localhost:8080' }}
      />
    );

    const toggleBtn = screen.getByRole('button', { name: /more info/i });
    expect(toggleBtn).toHaveAttribute('aria-expanded', 'false');
    expect(screen.queryByText('Technical Details')).not.toBeInTheDocument();

    fireEvent.click(toggleBtn);

    expect(toggleBtn).toHaveAttribute('aria-expanded', 'true');
    expect(screen.getByText('Less info')).toBeInTheDocument();
    expect(screen.getByText('Technical Details')).toBeInTheDocument();
    expect(screen.getByText(/"code": 500/)).toBeInTheDocument();

    fireEvent.click(toggleBtn);
    expect(screen.queryByText('Technical Details')).not.toBeInTheDocument();
  });

  it('copies details to clipboard when Copy button is clicked', async () => {
    mockWriteText.mockResolvedValueOnce(undefined);

    render(
      <ContextualError
        message="RPC Error"
        details="Make sure the node is running"
      />
    );

    fireEvent.click(screen.getByRole('button', { name: /more info/i }));
    fireEvent.click(screen.getByRole('button', { name: /copy/i }));

    await waitFor(() => {
      expect(mockWriteText).toHaveBeenCalledWith(
        'Make sure the node is running'
      );
      expect(screen.getByText('Copied!')).toBeInTheDocument();
    });
  });
});
