// TypeScript representation of a Bead/Share from the node crate

export interface BlockHeader {
  version: number;
  prevBlockHash: string;
  merkleRoot: string;
  timestamp: number;
  bits: number;
  nonce: number;
}

export interface Transaction {
  txid: string;
  version: number;
  lockTime: number;
  size: number;
  weight: number;
  inputs: TransactionInput[];
  outputs: TransactionOutput[];
}

export interface TransactionInput {
  prevTxId: string;
  prevVout: number;
  scriptSig: string;
  sequence: number;
}

export interface TransactionOutput {
  value: number;
  scriptPubKey: string;
}

export interface MerklePathProof {
  txIndex: number;
  siblings: string[];
}

export interface TransactionWithMerklePath {
  transaction: Transaction;
  merkleProof: MerklePathProof;
}

export interface BeadParent {
  beadHash: string;
  timestamp: number;
}

export interface Bead {
  // Core bead properties
  blockHeader: BlockHeader;
  beadHash: string;
  coinbaseTransaction: TransactionWithMerklePath;
  payoutUpdateTransaction: TransactionWithMerklePath;

  // Braidpool metadata
  lesserDifficultyTarget: number;
  parents: BeadParent[];
  transactions: Transaction[];

  // Node information
  observedTimeAtNode: number;

  // Additional UI-specific properties
  isTip?: boolean;
  isGenesis?: boolean;
  cohortId?: number;
  depth?: number;
}

// Separate interface for the UI component that might contain additional display information
export interface BeadDisplayData extends Bead {
  formattedHash?: string;
  formattedTimestamp?: string;
  validationStatus?: 'valid' | 'invalid' | 'pending';
  childrenCount?: number;
}
