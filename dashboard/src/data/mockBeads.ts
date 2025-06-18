import { Bead, BeadDisplayData } from '../types/Bead';

// Helper function to create a shortened version of a hash for display
const shortenHash = (hash: string): string => {
  if (hash.length <= 12) return hash;
  return `${hash.substring(0, 6)}...${hash.substring(hash.length - 6)}`;
};

// Helper function to format timestamp as readable date
const formatTimestamp = (timestamp: number): string => {
  return new Date(timestamp).toLocaleString();
};

// Create a basic mock transaction
const createMockTransaction = (id: string, isGenesis: boolean = false) => {
  return {
    txid: `tx${id}`,
    version: 1,
    lockTime: 0,
    size: 225,
    weight: 900,
    inputs: isGenesis
      ? []
      : [
          {
            prevTxId: `prev${id}`,
            prevVout: 0,
            scriptSig: 'scriptSig',
            sequence: 4294967295,
          },
        ],
    outputs: [
      {
        value: 50,
        scriptPubKey: 'scriptPubKey',
      },
    ],
  };
};

// Create a mock transaction with Merkle path
const createMockTxWithMerklePath = (id: string, isGenesis: boolean = false) => {
  return {
    transaction: createMockTransaction(id, isGenesis),
    merkleProof: {
      txIndex: 0,
      siblings: [`sibling1_${id}`, `sibling2_${id}`],
    },
  };
};

// Base timestamp for our mock data
const now = Date.now();

// Genesis bead mock data
export const genesisBeadMock: BeadDisplayData = {
  blockHeader: {
    version: 1,
    prevBlockHash:
      '0000000000000000000000000000000000000000000000000000000000000000',
    merkleRoot:
      '4a5e1e4baab89f3a32518a88c31bc87f618f76673e2cc77ab2127b7afdeda33b',
    timestamp: now - 86400000 * 30, // 30 days ago
    bits: 486604799,
    nonce: 2083236893,
  },
  beadHash: '000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f',
  coinbaseTransaction: createMockTxWithMerklePath('genesis_coinbase', true),
  payoutUpdateTransaction: createMockTxWithMerklePath('genesis_payout', true),
  lesserDifficultyTarget: 486604799,
  parents: [],
  transactions: [createMockTransaction('genesis_1', true)],
  observedTimeAtNode: now - 86400000 * 30,

  // UI-specific properties
  formattedHash: shortenHash(
    '000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f'
  ),
  formattedTimestamp: formatTimestamp(now - 86400000 * 30),
  validationStatus: 'valid',
  childrenCount: 2,
  isGenesis: true,
  cohortId: 0,
  depth: 0,
};

// Regular bead mock data
export const regularBeadMock: BeadDisplayData = {
  blockHeader: {
    version: 1,
    prevBlockHash:
      '000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f',
    merkleRoot:
      '9b0fc92260312ce44e74ef369f5c66bbb85848f2eddd5a7a1cde251e54ccfdd5',
    timestamp: now - 86400000 * 15, // 15 days ago
    bits: 486604799,
    nonce: 1234567890,
  },
  beadHash: '00000000839a8e6886ab5951d76f411475428afc90947ee320161bbf18eb6048',
  coinbaseTransaction: createMockTxWithMerklePath('regular_coinbase'),
  payoutUpdateTransaction: createMockTxWithMerklePath('regular_payout'),
  lesserDifficultyTarget: 486604799,
  parents: [
    {
      beadHash:
        '000000000019d6689c085ae165831e934ff763ae46a2a6c172b3f1b60a8ce26f',
      timestamp: now - 86400000 * 30,
    },
  ],
  transactions: [
    createMockTransaction('regular_1'),
    createMockTransaction('regular_2'),
  ],
  observedTimeAtNode: now - 86400000 * 15,

  // UI-specific properties
  formattedHash: shortenHash(
    '00000000839a8e6886ab5951d76f411475428afc90947ee320161bbf18eb6048'
  ),
  formattedTimestamp: formatTimestamp(now - 86400000 * 15),
  validationStatus: 'valid',
  childrenCount: 3,
  cohortId: 1,
  depth: 1,
};

// Tip bead mock data (a bead with no children)
export const tipBeadMock: BeadDisplayData = {
  blockHeader: {
    version: 1,
    prevBlockHash:
      '00000000839a8e6886ab5951d76f411475428afc90947ee320161bbf18eb6048',
    merkleRoot:
      '7dac2c5666815c17a3b36427de37bb9d2e2c5ccec3f8633eb91a4205cb4c10ff',
    timestamp: now - 86400000 * 1, // 1 day ago
    bits: 486604799,
    nonce: 987654321,
  },
  beadHash: '000000006a625f06636b8bb6ac7b960a8d03705d1ace08b1a19da3fdcc99ddbd',
  coinbaseTransaction: createMockTxWithMerklePath('tip_coinbase'),
  payoutUpdateTransaction: createMockTxWithMerklePath('tip_payout'),
  lesserDifficultyTarget: 486604799,
  parents: [
    {
      beadHash:
        '00000000839a8e6886ab5951d76f411475428afc90947ee320161bbf18eb6048',
      timestamp: now - 86400000 * 15,
    },
  ],
  transactions: [
    createMockTransaction('tip_1'),
    createMockTransaction('tip_2'),
    createMockTransaction('tip_3'),
  ],
  observedTimeAtNode: now - 86400000 * 1,

  // UI-specific properties
  formattedHash: shortenHash(
    '000000006a625f06636b8bb6ac7b960a8d03705d1ace08b1a19da3fdcc99ddbd'
  ),
  formattedTimestamp: formatTimestamp(now - 86400000 * 1),
  validationStatus: 'valid',
  childrenCount: 0,
  isTip: true,
  cohortId: 2,
  depth: 2,
};

// Collection of all mock beads for easy access
export const mockBeads: Record<string, BeadDisplayData> = {
  genesis: genesisBeadMock,
  regular: regularBeadMock,
  tip: tipBeadMock,
};

// Function to get a bead by hash
export const getBeadByHash = (hash: string): BeadDisplayData | undefined => {
  // In a real implementation, this would call the API
  return Object.values(mockBeads).find((bead) => bead.beadHash === hash);
};

// Export a helpful print statement to be used during development
export const printDebug = () => {
  console.log('🔍 Using mock bead data', mockBeads);
};
