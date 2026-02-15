import React from 'react';

interface Props {
  error: Error | null;
  onReset: () => void;
}

/**
 * ErrorFallback component - UI displayed when an error is caught by ErrorBoundary.
 * Provides a friendly error message and recovery options.
 */
const ErrorFallback: React.FC<Props> = ({ error, onReset }) => {
  const isDevelopment = process.env.NODE_ENV === 'development';

  const handleGoHome = (): void => {
    window.location.href = '/';
  };

  return (
    <div
      className="min-h-[400px] flex items-center justify-center p-4"
      role="alert"
      aria-live="assertive"
    >
      <div className="max-w-lg w-full bg-gray-800 border border-red-500/50 rounded-xl p-8 shadow-2xl">
        {/* Error Icon */}
        <div className="flex justify-center mb-6">
          <div className="w-16 h-16 bg-red-500/20 rounded-full flex items-center justify-center">
            <svg
              className="w-8 h-8 text-red-500"
              fill="none"
              stroke="currentColor"
              viewBox="0 0 24 24"
              aria-hidden="true"
            >
              <path
                strokeLinecap="round"
                strokeLinejoin="round"
                strokeWidth={2}
                d="M12 9v2m0 4h.01m-6.938 4h13.856c1.54 0 2.502-1.667 1.732-3L13.732 4c-.77-1.333-2.694-1.333-3.464 0L3.34 16c-.77 1.333.192 3 1.732 3z"
              />
            </svg>
          </div>
        </div>

        {/* Title */}
        <h2 className="text-2xl font-bold text-white text-center mb-2">
          Something Went Wrong
        </h2>

        {/* Description */}
        <p className="text-gray-400 text-center mb-6">
          We encountered an error loading this page. Our team has been notified.
        </p>

        {/* Error Details (Development Only) */}
        {isDevelopment && error && (
          <div className="mb-6 p-4 bg-red-900/30 border border-red-500/30 rounded-lg">
            <p className="text-red-400 text-sm font-mono break-all">
              <span className="font-bold">Error:</span> {error.message}
            </p>
            {error.stack && (
              <details className="mt-2">
                <summary className="text-red-400 text-sm cursor-pointer hover:text-red-300">
                  Stack Trace
                </summary>
                <pre className="mt-2 text-xs text-red-300 overflow-x-auto">
                  {error.stack}
                </pre>
              </details>
            )}
          </div>
        )}

        {/* Action Buttons */}
        <div className="flex flex-col sm:flex-row gap-3 justify-center">
          <button
            onClick={onReset}
            className="px-6 py-3 bg-blue-600 hover:bg-blue-700 text-white font-medium rounded-lg transition-colors focus:outline-none focus:ring-2 focus:ring-blue-500 focus:ring-offset-2 focus:ring-offset-gray-800"
            aria-label="Try loading the page again"
          >
            Try Again
          </button>
          <button
            onClick={handleGoHome}
            className="px-6 py-3 bg-gray-700 hover:bg-gray-600 text-white font-medium rounded-lg transition-colors focus:outline-none focus:ring-2 focus:ring-gray-500 focus:ring-offset-2 focus:ring-offset-gray-800"
            aria-label="Go to dashboard home"
          >
            Go to Dashboard
          </button>
        </div>

        {/* Footer Note */}
        <p className="text-gray-500 text-xs text-center mt-6">
          If this problem persists, please try refreshing the page or contact
          support.
        </p>
      </div>
    </div>
  );
};

export default ErrorFallback;
