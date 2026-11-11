import React, { useState } from 'react';
import { AlertCircle, ChevronDown, Copy, Download } from 'lucide-react';

interface ContextualErrorProps {
  message: string;
  details?: unknown;
  timestamp?: Date;
}

const ContextualError: React.FC<ContextualErrorProps> = ({
  message,
  details,
  timestamp,
}) => {
  const [showDetails, setShowDetails] = useState(false);
  const [copied, setCopied] = useState(false);
  const [defaultTimestamp] = useState(() => new Date());

  const formatDetails = (data: unknown): string => {
    if (typeof data === 'string') return data;
    try {
      return JSON.stringify(data, null, 2);
    } catch {
      return String(data);
    }
  };

  const detailsText = details ? formatDetails(details) : '';

  const handleCopy = async () => {
    try {
      await navigator.clipboard.writeText(detailsText);
      setCopied(true);
      setTimeout(() => setCopied(false), 2000);
    } catch {
      // Fallback: clipboard API may not be available in all contexts
    }
  };

  const handleDownload = () => {
    const blob = new Blob([detailsText], { type: 'text/plain' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `error_log_${new Date().toISOString()}.txt`;
    document.body.appendChild(a);
    a.click();
    document.body.removeChild(a);
    URL.revokeObjectURL(url);
  };

  const displayTimestamp = timestamp ?? defaultTimestamp;

  return (
    <div className="bg-red-900/20 border border-red-500/50 rounded-lg p-4 mb-4 text-red-200 w-full max-w-4xl mx-auto">
      <div className="flex items-start justify-between">
        <div className="flex items-center gap-2">
          <AlertCircle className="w-5 h-5 text-red-400 flex-shrink-0" />
          <span className="font-medium text-red-100">{message}</span>
        </div>

        {!!details && (
          <button
            onClick={() => setShowDetails(!showDetails)}
            aria-expanded={showDetails}
            className="flex items-center gap-1 text-sm text-red-300 hover:text-red-100 transition-colors bg-red-900/30 px-2 py-1 rounded cursor-pointer"
          >
            {showDetails ? 'Less info' : 'More info'}
            <ChevronDown
              className={`w-4 h-4 transition-transform ${showDetails ? 'rotate-180' : ''}`}
            />
          </button>
        )}
      </div>

      {!!details && showDetails && (
        <div className="mt-4 pt-4 border-t border-red-500/30">
          <div className="flex justify-between items-center mb-2">
            <div className="flex items-center gap-3">
              <span className="text-xs text-red-400 font-semibold uppercase tracking-wider">
                Technical Details
              </span>
              <span className="text-xs text-red-400/70">
                {displayTimestamp.toLocaleString()}
              </span>
            </div>
            <div className="flex gap-2">
              <button
                onClick={handleCopy}
                className="flex items-center gap-1 text-xs bg-red-900/50 hover:bg-red-800/80 px-2 py-1 rounded text-red-200 transition-colors cursor-pointer"
              >
                <Copy className="w-3 h-3" />
                {copied ? 'Copied!' : 'Copy'}
              </button>
              <button
                onClick={handleDownload}
                className="flex items-center gap-1 text-xs bg-red-900/50 hover:bg-red-800/80 px-2 py-1 rounded text-red-200 transition-colors cursor-pointer"
              >
                <Download className="w-3 h-3" />
                Download
              </button>
            </div>
          </div>
          <pre className="bg-black/40 p-3 rounded text-xs text-red-200 font-mono overflow-x-auto whitespace-pre-wrap text-left">
            {detailsText}
          </pre>
        </div>
      )}
    </div>
  );
};

export default ContextualError;
