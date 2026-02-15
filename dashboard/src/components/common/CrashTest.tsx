import React from 'react';

/**
 * Test component to demonstrate error boundary need.
 * This component intentionally throws an error when the button is clicked.
 */
const CrashTest: React.FC = () => {
  const [shouldCrash, setShouldCrash] = React.useState(false);

  if (shouldCrash) {
    // Intentionally throw an error to demonstrate the crash
    throw new Error(
      '💥 Intentional test crash! This proves the dashboard needs an Error Boundary.'
    );
  }

  return (
    <div className="p-6 bg-red-900/20 border border-red-500 rounded-lg">
      <h3 className="text-red-400 font-bold mb-2">
        🧪 Error Boundary Test Component
      </h3>
      <p className="text-gray-300 mb-4 text-sm">
        Click the button below to simulate a runtime error in a child component.
        Without an Error Boundary, this will crash the entire dashboard and show
        a blank screen.
      </p>
      <button
        onClick={() => setShouldCrash(true)}
        className="px-4 py-2 bg-red-600 hover:bg-red-700 text-white rounded transition-colors"
      >
        💥 Trigger Crash
      </button>
    </div>
  );
};

export default CrashTest;
