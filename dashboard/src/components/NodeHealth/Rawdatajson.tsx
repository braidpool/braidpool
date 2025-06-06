'use client';

import { useState } from 'react';
import { ChevronDown } from 'lucide-react';
import { RawJsonViewerProps } from './__tests__/types';

export default function RawJsonViewer({
  data,
  title = 'Raw Data',
}: RawJsonViewerProps) {
  const [showJson, setShowJson] = useState(false);

  return (
    <div className="bg-[#1c1c1c] mt-10 border border-gray-700 rounded-lg p-6 backdrop-blur-sm">
      <div className="mb-4">
        <h2 className="text-xl font-semibold text-white">{title}</h2>
      </div>

      <button
        onClick={() => setShowJson(!showJson)}
        className="w-full flex items-center justify-between px-4 py-2 border border-gray-600 text-gray-300 rounded hover:bg-gray-700 transition"
      >
        View JSON
        <ChevronDown
          className={`w-4 h-4 transition-transform ${showJson ? 'rotate-180' : ''}`}
        />
      </button>

      {showJson && (
        <pre className="mt-4 text-xs bg-gray-900/50 text-gray-300 p-4 rounded-lg overflow-auto max-h-96 border border-gray-700">
          {JSON.stringify(data, null, 2)}
        </pre>
      )}
    </div>
  );
}
