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
  bead_count: number;
}

export interface Position {
  x: number;
  y: number;
}

export var COLORS = [
  `rgba(${217}, ${95}, ${2}, 1)`,
  `rgba(${117}, ${112}, ${179}, 1)`,
  `rgba(${102}, ${166}, ${30}, 1)`,
  `rgba(${231}, ${41}, ${138}, 1)`,
];
