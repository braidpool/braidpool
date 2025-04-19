import React, { useState, useEffect } from 'react';

interface Transaction {
  txid: string;
  size: number;
  fee: number;
  timeReceived: number;
  priority: string;
}

const PendingTransactions: React.FC = () => {
  const [transactions, setTransactions] = useState<Transaction[]>([]);
  const [loading, setLoading] = useState(true);
  const [totalTxs, setTotalTxs] = useState(0);
  const [memPoolSize, setMemPoolSize] = useState(0);

  useEffect(() => {
    const fetchTransactions = async () => {
      try {
        console.log('🔍 Fetching pending transactions...');
        // Simulated data fetch - would be an API call in production
        setTimeout(() => {
          const mockTxs: Transaction[] = [
            {
              txid: '7a4c376a387d6b6fce83d5f22e25f43c6d5d5095886b71c9ff0f4acd25a3d9a4',
              size: 234,
              fee: 0.00015,
              timeReceived: Date.now() - 500000,
              priority: 'high',
            },
            {
              txid: '3d29864384c86eea4f122a41e685db2cf8d0dca71afc7b8696a499902d1ad11e',
              size: 543,
              fee: 0.00023,
              timeReceived: Date.now() - 300000,
              priority: 'high',
            },
            {
              txid: '42ec3e7a6d7b12f251cc7ca129b8c911e79348e9c9abe5f3dc35f1bdbb71f94c',
              size: 176,
              fee: 0.00008,
              timeReceived: Date.now() - 100000,
              priority: 'medium',
            },
            {
              txid: '910acf3ca4e94f32b5cb5493c6a3cd6bfccff13a78d07befe164db772e6993b7',
              size: 219,
              fee: 0.00004,
              timeReceived: Date.now() - 50000,
              priority: 'low',
            },
          ];

          setTransactions(mockTxs);
          setTotalTxs(2483);
          setMemPoolSize(34.8);
          setLoading(false);
          console.log('✅ Loaded pending transactions!');
        }, 1200);
      } catch (error) {
        console.error('💥 Error fetching transactions:', error);
        setLoading(false);
      }
    };

    fetchTransactions();
  }, []);

  // Format timestamp to readable time
  const formatTime = (timestamp: number): string => {
    const seconds = Math.floor((Date.now() - timestamp) / 1000);

    if (seconds < 60) return `${seconds}s ago`;
    if (seconds < 3600) return `${Math.floor(seconds / 60)}m ago`;
    return `${Math.floor(seconds / 3600)}h ago`;
  };

  if (loading) {
    return <div>Loading transaction data...</div>;
  }

  return (
    <div className='pending-transactions'>
      <h2>Transaction Pool</h2>

      <div className='transaction-stats'>
        <div className='stat-card'>
          <h3>Pending Transactions</h3>
          <p>{totalTxs}</p>
        </div>
        <div className='stat-card'>
          <h3>Mempool Size</h3>
          <p>{memPoolSize} MB</p>
        </div>
      </div>

      <h3>Recent Transactions</h3>
      <table className='transactions-table'>
        <thead>
          <tr>
            <th>Transaction ID</th>
            <th>Size (bytes)</th>
            <th>Fee (BTC)</th>
            <th>Time</th>
            <th>Priority</th>
          </tr>
        </thead>
        <tbody>
          {transactions.map((tx) => (
            <tr key={tx.txid}>
              <td>
                <span className='tx-id'>{`${tx.txid.substring(
                  0,
                  8
                )}...${tx.txid.substring(tx.txid.length - 8)}`}</span>
              </td>
              <td>{tx.size}</td>
              <td>{tx.fee.toFixed(5)}</td>
              <td>{formatTime(tx.timeReceived)}</td>
              <td>
                <span className={`priority-tag priority-${tx.priority}`}>
                  {tx.priority}
                </span>
              </td>
            </tr>
          ))}
        </tbody>
      </table>

      <div className='transaction-actions'>
        <button>Refresh</button>
        <button>View All</button>
      </div>
    </div>
  );
};

export default PendingTransactions;
