export interface GraphNode {
  id: string;
  parents: string[];
  children: string[];
}

export interface NodeIdMapping {
  [hash: string]: string; // maps hash to sequential ID
}

export interface GraphData {
  highestWorkPath: string[];
  parents: Record<string, string[]>;
  children: Record<string, string[]>;
  cohorts: string[][];
  bead_count: number;
}

export interface Position {
  x: number;
  y: number;
}
