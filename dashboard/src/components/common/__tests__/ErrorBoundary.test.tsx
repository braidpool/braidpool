import React from 'react';
import { render, screen, fireEvent, waitFor } from '@testing-library/react';
import '@testing-library/jest-dom';
import ErrorBoundary from '../ErrorBoundary';

// Component that throws an error
const ThrowError: React.FC<{ shouldThrow?: boolean }> = ({ shouldThrow }) => {
  if (shouldThrow) {
    throw new Error('Test error');
  }
  return <div>No error</div>;
};

// Component that throws after update
const ThrowAfterUpdate: React.FC<{ triggerError: boolean }> = ({
  triggerError,
}) => {
  if (triggerError) {
    throw new Error('Runtime error');
  }
  return <div>Component rendered</div>;
};

// Mock console.error to avoid noise in test output
const originalConsoleError = console.error;
beforeAll(() => {
  console.error = jest.fn();
});

afterAll(() => {
  console.error = originalConsoleError;
});

// Helper to wait for retry delay (default 2 seconds)
const waitForRetryDelay = () =>
  new Promise((resolve) => setTimeout(resolve, 2100));

describe('ErrorBoundary', () => {
  beforeEach(() => {
    jest.clearAllMocks();
  });

  describe('when there is no error', () => {
    it('renders children normally', () => {
      render(
        <ErrorBoundary>
          <div data-testid="child">Child content</div>
        </ErrorBoundary>
      );

      expect(screen.getByTestId('child')).toBeInTheDocument();
      expect(screen.getByText('Child content')).toBeInTheDocument();
    });
  });

  describe('when an error is thrown', () => {
    it('catches the error and displays fallback UI', () => {
      render(
        <ErrorBoundary>
          <ThrowError shouldThrow={true} />
        </ErrorBoundary>
      );

      // Should show error fallback UI
      expect(screen.getByText(/Something Went Wrong/i)).toBeInTheDocument();
      expect(screen.getByText(/We encountered an error/i)).toBeInTheDocument();
      expect(
        screen.getByText(/Clicking retry will re-attempt to render/i)
      ).toBeInTheDocument();
      expect(screen.getByRole('alert')).toBeInTheDocument();
    });

    it('does not render children after error', () => {
      render(
        <ErrorBoundary>
          <ThrowError shouldThrow={true} />
        </ErrorBoundary>
      );

      // Should not show the normal child content
      expect(screen.queryByText('No error')).not.toBeInTheDocument();
    });

    it('logs error to console', () => {
      render(
        <ErrorBoundary>
          <ThrowError shouldThrow={true} />
        </ErrorBoundary>
      );

      // Console.error should have been called
      expect(console.error).toHaveBeenCalled();
      const calls = (console.error as jest.Mock).mock.calls;
      const errorCall = calls.find(
        (call) =>
          typeof call[0] === 'string' &&
          call[0].includes('ErrorBoundary caught')
      );
      expect(errorCall).toBeTruthy();
    });
  });

  describe('error recovery', () => {
    it('calls onReset when try again button is clicked after delay', async () => {
      const onResetMock = jest.fn();

      render(
        <ErrorBoundary onReset={onResetMock}>
          <ThrowAfterUpdate triggerError={true} />
        </ErrorBoundary>
      );

      // Verify error state
      expect(screen.getByText(/Something Went Wrong/i)).toBeInTheDocument();

      // Wait for the retry delay (2 seconds)
      await waitForRetryDelay();

      // Click try again button (get by role since text includes countdown)
      const tryAgainButton = screen.getByRole('button', {
        name: /Retry rendering this section/i,
      });
      fireEvent.click(tryAgainButton);

      // onReset should have been called after the internal delay (2s retryDelay)
      await waitFor(
        () => {
          expect(onResetMock).toHaveBeenCalledTimes(1);
        },
        { timeout: 5000 }
      );
    });

    it('successfully recovers when the error cause is resolved and retry is clicked', async () => {
      const onResetMock = jest.fn();

      // We'll update triggerError from true -> false to simulate fixing the error
      const { rerender } = render(
        <ErrorBoundary onReset={onResetMock}>
          <ThrowAfterUpdate triggerError={true} />
        </ErrorBoundary>
      );

      // Verify it's initially in the error state
      expect(screen.getByText(/Something Went Wrong/i)).toBeInTheDocument();

      // "Fix" the underlying component so it no longer throws
      rerender(
        <ErrorBoundary onReset={onResetMock}>
          <ThrowAfterUpdate triggerError={false} />
        </ErrorBoundary>
      );

      // It still shows the error because ErrorBoundary hasn't been reset yet
      expect(screen.getByText(/Something Went Wrong/i)).toBeInTheDocument();

      // Wait for countdown and click retry
      await waitForRetryDelay();
      const retryBtn = screen.getByRole('button', {
        name: /Retry rendering this section/i,
      });
      fireEvent.click(retryBtn);

      // Wait for the ErrorBoundary's internal reset delay to complete
      await waitFor(
        () => {
          // It should successfully render the child component's content now
          expect(screen.getByText('Component rendered')).toBeInTheDocument();
        },
        { timeout: 5000 }
      );

      // The error boundary fallback should be gone
      expect(
        screen.queryByText(/Something Went Wrong/i)
      ).not.toBeInTheDocument();
      expect(onResetMock).toHaveBeenCalledTimes(1);
    }, 10000);

    it('disables try again button after max retries reached', async () => {
      const onResetMock = jest.fn();

      render(
        <ErrorBoundary onReset={onResetMock} maxRetries={3}>
          <ThrowAfterUpdate triggerError={true} />
        </ErrorBoundary>
      );

      // First error (retryCount=1): should be able to retry
      await waitFor(() => {
        expect(screen.getByText(/Attempt 1 of 3/i)).toBeInTheDocument();
      });

      // Wait for countdown and click the retry button as soon as it's available
      const retryBtn1 = await screen.findByRole(
        'button',
        { name: /Retry rendering this section/i },
        { timeout: 5000 }
      );
      fireEvent.click(retryBtn1);

      // Wait for reset delay + child re-throw → Attempt 2
      await waitFor(
        () => {
          expect(screen.getByText(/Attempt 2 of 3/i)).toBeInTheDocument();
        },
        { timeout: 5000 }
      );

      // Wait for countdown and click retry again
      const retryBtn2 = await screen.findByRole(
        'button',
        { name: /Retry rendering this section/i },
        { timeout: 5000 }
      );
      fireEvent.click(retryBtn2);

      // Wait for reset delay + child re-throw → Attempt 3 (exceeds max)
      await waitFor(
        () => {
          expect(screen.getByText(/Attempt 3 of 3/i)).toBeInTheDocument();
        },
        { timeout: 5000 }
      );

      // Should show max retries messaging and disabled button
      expect(
        screen.getByText(/Maximum retry attempts reached/i)
      ).toBeInTheDocument();
      expect(
        screen.getByText(/connection or server problem/i)
      ).toBeInTheDocument();

      // Wait for the countdown to finish so the aria-label changes to "Maximum retries reached"
      await waitFor(
        () => {
          expect(
            screen.getByRole('button', { name: /Maximum retries reached/i })
          ).toBeDisabled();
        },
        { timeout: 5000 }
      );
    }, 30000);

    it('shows retry countdown timer', async () => {
      render(
        <ErrorBoundary>
          <ThrowError shouldThrow={true} />
        </ErrorBoundary>
      );

      // Initially shows countdown
      expect(screen.getByText(/Retry \(2s\)/i)).toBeInTheDocument();

      // Wait a bit
      await new Promise((resolve) => setTimeout(resolve, 1100));

      // Should show 1s
      expect(screen.getByText(/Retry \(1s\)/i)).toBeInTheDocument();

      // Wait more
      await new Promise((resolve) => setTimeout(resolve, 1100));

      // Should show normal button
      expect(screen.getByText(/^Retry$/i)).toBeInTheDocument();
    });
  });

  describe('accessibility', () => {
    it('has role="alert" for screen readers', () => {
      render(
        <ErrorBoundary>
          <ThrowError shouldThrow={true} />
        </ErrorBoundary>
      );

      const alert = screen.getByRole('alert');
      expect(alert).toBeInTheDocument();
    });

    it('has aria-live="assertive" for announcements', () => {
      render(
        <ErrorBoundary>
          <ThrowError shouldThrow={true} />
        </ErrorBoundary>
      );

      const alert = screen.getByRole('alert');
      expect(alert).toHaveAttribute('aria-live', 'assertive');
    });

    it('has accessible button labels', async () => {
      render(
        <ErrorBoundary>
          <ThrowError shouldThrow={true} />
        </ErrorBoundary>
      );

      // Initially the button shows countdown in aria-label
      expect(
        screen.getByRole('button', { name: /Retry in \d+ seconds/i })
      ).toBeInTheDocument();
      expect(
        screen.getByRole('button', { name: /Go to dashboard home/i })
      ).toBeInTheDocument();

      // Wait for countdown to finish
      await waitForRetryDelay();

      // After countdown, button shows standard label
      expect(
        screen.getByRole('button', { name: /Retry rendering this section/i })
      ).toBeInTheDocument();
    });
  });

  describe('custom fallback', () => {
    it('renders custom fallback when provided', () => {
      const customFallback = (
        <div data-testid="custom-fallback">Custom error UI</div>
      );

      render(
        <ErrorBoundary fallback={customFallback}>
          <ThrowError shouldThrow={true} />
        </ErrorBoundary>
      );

      expect(screen.getByTestId('custom-fallback')).toBeInTheDocument();
      expect(screen.getByText('Custom error UI')).toBeInTheDocument();
    });
  });

  describe('onError callback', () => {
    it('calls onError when error is caught', () => {
      const onErrorMock = jest.fn();

      render(
        <ErrorBoundary onError={onErrorMock}>
          <ThrowError shouldThrow={true} />
        </ErrorBoundary>
      );

      expect(onErrorMock).toHaveBeenCalledTimes(1);
      expect(onErrorMock).toHaveBeenCalledWith(
        expect.any(Error),
        expect.objectContaining({
          componentStack: expect.any(String),
        })
      );

      // Verify the error message
      const [error] = onErrorMock.mock.calls[0];
      expect(error.message).toBe('Test error');
    });
  });
});
