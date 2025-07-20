import { useState, useMemo } from 'react';
import { PeerInfo } from './Types';
import { formatBytes, paginate, calculateTotalPages } from './Utils';

const ITEMS_PER_PAGE = 10;

export default function Peers({ peers }: { peers: PeerInfo[] }) {
  const [currentPage, setCurrentPage] = useState(1);
  const totalPages = useMemo(
    () => calculateTotalPages(peers.length, ITEMS_PER_PAGE),
    [peers.length]
  );

  const paginatedPeers = paginate(peers, currentPage, ITEMS_PER_PAGE);
  const handlePrev = () => {
    setCurrentPage((prev) => Math.max(prev - 1, 1));
  };

  const handleNext = () => {
    setCurrentPage((prev) => Math.min(prev + 1, totalPages));
  };

  return (
    <div className="bg-[#1e1e1e] border border-gray-700 rounded-xl shadow-md">
      <div className="px-6 py-4 border-b border-gray-700">
        <h2 className="text-white text-xl font-semibold">Connected Peers</h2>
        <p className="text-gray-300 text-sm">
          {peers.length} total peers connected
        </p>
      </div>

      <div className="px-6 py-4 space-y-4">
        {paginatedPeers.map((peer) => (
          <div
            key={peer.id}
            className="grid max-sm:grid-cols-1 md:grid-cols-2 p-4 border border-gray-700 rounded-lg bg-gray-900/30 hover:bg-gray-900/50 transition-colors overflow-x-hidden"
          >
            <div className="space-y-1">
              <p className="text-white font-medium">{peer.addr}</p>
              <div
                className="flex  max-sm:flex-col md:flex-row 
               items-start sm:items-center gap-1 sm:gap-2"
              >
                <span
                  className={`px-2 py-0.5 rounded-full text-xs font-medium ${
                    peer.inbound
                      ? 'bg-gray-600 text-gray-200'
                      : 'bg-blue-600 text-white'
                  }`}
                >
                  {peer.inbound ? 'Inbound' : 'Outbound'}
                </span>
                <span className="text-sm text-gray-400 ">
                  Version : {peer.subver}
                </span>
              </div>
            </div>
            <div className="text-right space-y-1">
              <p className="text-sm font-medium text-white">
                Ping: {peer.pingtime}ms
              </p>
              <p className="text-xs text-gray-400">
                ↑ {formatBytes(peer.bytessent)} ↓ {formatBytes(peer.bytesrecv)}
              </p>
            </div>
          </div>
        ))}
        {[...Array(ITEMS_PER_PAGE - paginatedPeers.length)].map((_, idx) => (
          <div
            key={`empty-${idx}`}
            className="p-4 border border-transparent rounded-lg"
          />
        ))}
      </div>

      {/* Pagination Controls */}
      <div className="px-6 py-4 flex justify-between items-center border-t border-gray-700 text-sm text-gray-300">
        <button
          onClick={handlePrev}
          disabled={currentPage === 1}
          className={`px-3 py-1 rounded ${currentPage === 1 ? 'opacity-50 cursor-not-allowed' : 'hover:bg-gray-800'}`}
        >
          Previous
        </button>

        <span>
          Page {currentPage} of {totalPages}
        </span>

        <button
          onClick={handleNext}
          disabled={currentPage === totalPages}
          className={`px-3 py-1 rounded ${currentPage === totalPages ? 'opacity-50 cursor-not-allowed' : 'hover:bg-gray-800'}`}
        >
          Next
        </button>
      </div>
    </div>
  );
}
