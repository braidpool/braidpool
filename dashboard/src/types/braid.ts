export interface BraidData {
  description: string;
  parents: Record<string, number[]>;
  children: Record<string, number[]>;
  tips: number[];
  cohorts: number[][];
}

export interface BraidNode {
  id: number;
  parents: number[];
  children: number[];
  cohort: number;
  isTip: boolean;
}

export interface BraidLink {
  source: number;
  target: number;
  isHighWorkPath?: boolean;
}

export interface BraidVisualizationData {
  nodes: BraidNode[];
  links: BraidLink[];
  cohorts: number[][];
}
