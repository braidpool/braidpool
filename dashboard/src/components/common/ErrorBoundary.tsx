import React, { Component, ErrorInfo, ReactNode } from 'react';
import ErrorFallback from './ErrorFallback';

interface Props {
  children: ReactNode;
  fallback?: ReactNode;
  onReset?: () => void;
  onError?: (error: Error, errorInfo: ErrorInfo) => void;
  maxRetries?: number;
  retryDelay?: number;
}

interface State {
  hasError: boolean;
  error: Error | null;
  retryCount: number;
  lastErrorTimestamp: number | null;
}

/**
 * Error Boundary component that catches JavaScript errors in child components.
 * Prevents the entire application from crashing when a single component fails.
 *
 * Usage:
 * <ErrorBoundary>
 *   <YourComponent />
 * </ErrorBoundary>
 *
 * @see https://react.dev/reference/react/Component#catching-rendering-errors-with-an-error-boundary
 */
class ErrorBoundary extends Component<Props, State> {
  private retryTimeoutId: number | null = null;

  constructor(props: Props) {
    super(props);
    this.state = {
      hasError: false,
      error: null,
      retryCount: 0,
      lastErrorTimestamp: null,
    };
  }

  componentWillUnmount(): void {
    if (this.retryTimeoutId !== null) {
      clearTimeout(this.retryTimeoutId);
    }
  }

  /**
   * Update state when an error is caught.
   * Note: React only passes the error argument to this static method.
   * retryCount is incremented in componentDidCatch which has access to instance state.
   */
  static getDerivedStateFromError(error: Error): Partial<State> {
    return {
      hasError: true,
      error,
      lastErrorTimestamp: Date.now(),
    };
  }

  /**
   * Log error details and increment retry count when an error is caught.
   * This method is called after the error is caught and has access to component state.
   */
  componentDidCatch(error: Error, errorInfo: ErrorInfo): void {
    // Increment retry count (cannot be done in getDerivedStateFromError as it's static)
    this.setState((prevState) => ({
      retryCount: prevState.retryCount + 1,
    }));

    // Log error to console for debugging
    console.error('ErrorBoundary caught an error:', error);
    console.error('Component stack:', errorInfo.componentStack);
    console.error('Retry count:', this.state.retryCount + 1);

    // Call optional onError callback for custom error handling
    // (e.g., sending to error tracking service like Sentry)
    if (this.props.onError) {
      this.props.onError(error, errorInfo);
    }
  }

  /**
   * Reset the error state to allow retry.
   * Includes an optional delay to prevent immediate re-crash loops.
   */
  resetErrorBoundary = (): void => {
    const { retryDelay = 2000 } = this.props;

    // Clear any existing timeout
    if (this.retryTimeoutId !== null) {
      clearTimeout(this.retryTimeoutId);
    }

    // Set a timeout before actually resetting to give user feedback
    this.retryTimeoutId = window.setTimeout(() => {
      this.setState({ hasError: false, error: null });

      // Call optional onReset callback
      if (this.props.onReset) {
        this.props.onReset();
      }
    }, retryDelay);
  };

  /**
   * Check if the user can still retry based on maxRetries.
   */
  canRetry = (): boolean => {
    const { maxRetries = 3 } = this.props;
    return this.state.retryCount < maxRetries;
  };

  render(): ReactNode {
    const { maxRetries = 3 } = this.props;
    const { retryCount } = this.state;

    if (this.state.hasError) {
      // Custom fallback UI was provided
      if (this.props.fallback) {
        return this.props.fallback;
      }

      // Default fallback UI with error details and retry information
      return (
        <ErrorFallback
          error={this.state.error}
          onReset={this.resetErrorBoundary}
          retryCount={retryCount}
          maxRetries={maxRetries}
          canRetry={this.canRetry()}
        />
      );
    }

    // No error - render children normally
    return this.props.children;
  }
}

export default ErrorBoundary;
