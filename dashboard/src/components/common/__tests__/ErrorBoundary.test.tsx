import React from 'react';
import { render, screen, fireEvent } from '@testing-library/react';
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
    it('calls onReset when try again button is clicked', () => {
      const onResetMock = jest.fn();

      const { rerender, unmount } = render(
        <ErrorBoundary onReset={onResetMock}>
          <ThrowAfterUpdate triggerError={true} />
        </ErrorBoundary>
      );

      // Verify error state
      expect(screen.getByText(/Something Went Wrong/i)).toBeInTheDocument();

      // Click try again button (get by visible text)
      const tryAgainButton = screen.getByText(/Try Again/i);
      fireEvent.click(tryAgainButton);

      // onReset should have been called
      expect(onResetMock).toHaveBeenCalledTimes(1);

      // Unmount and remount with no error to fully reset
      unmount();
      render(
        <ErrorBoundary onReset={onResetMock}>
          <ThrowAfterUpdate triggerError={false} />
        </ErrorBoundary>
      );

      // Should show normal content
      expect(screen.getByText('Component rendered')).toBeInTheDocument();
    });

    it('has Go to Dashboard button that navigates', () => {
      render(
        <ErrorBoundary>
          <ThrowError shouldThrow={true} />
        </ErrorBoundary>
      );

      // Click go home button (get by visible text)
      const goHomeButton = screen.getByText(/Go to Dashboard/i);
      expect(goHomeButton).toBeInTheDocument();
      expect(goHomeButton.tagName).toBe('BUTTON');
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

    it('has accessible button labels', () => {
      render(
        <ErrorBoundary>
          <ThrowError shouldThrow={true} />
        </ErrorBoundary>
      );

      expect(
        screen.getByRole('button', { name: /Try loading the page again/i })
      ).toBeInTheDocument();
      expect(
        screen.getByRole('button', { name: /Go to dashboard home/i })
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
