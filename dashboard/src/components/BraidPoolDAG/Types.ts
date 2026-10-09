export interface GraphNode {
  id: string;
  parents: string[];
  children: string[];
}

export interface NodeIdMapping {
  [hash: string]: string; // maps hash to sequential ID
}

export interface GraphData {
  highest_work_path: string[];
  parents: Record<string, string[]>;
  children: Record<string, string[]>;
  cohorts: string[][];
  cohort_start_index: number;
  bead_count: number;
  timestamps?: Record<string, number | null>;
}

export interface Position {
  x: number;
  y: number;
}

export interface BeadRecord {
  hash: string;
  parentHashes: string[];
  parentCount: number;
  childHashes: string[];
  childCount: number;
  isHWP: boolean | null;
  timestamp: number | null;
  cohortIndex: number;
}
