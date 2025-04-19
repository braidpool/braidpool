import * as PIXI from 'pixi.js';
import { Socket } from 'socket.io-client';

export interface GraphNode {
  id: string;
  parents: string[];
  children: string[];
  work?: number;
}

export interface NodeIdMapping {
  [hash: string]: string; // maps hash to sequential ID
}

export interface GraphData {
  highest_work_path: string[];
  parents: Record<string, string[]>;
  children: Record<string, string[]>;
  work?: Record<string, number>;
  cohorts: string[][];
  bead_count: number;
}

export interface Position {
  x: number;
  y: number;
}

export interface ConnectionStatus {
  connected: boolean;
  status:
    | 'Connecting'
    | 'Connected'
    | 'Disconnected'
    | 'Error'
    | 'Retrying'
    | 'Failed'
    | 'Active';
  message: string;
}

export interface PixiRendererProps {
  containerElement: HTMLDivElement;
  graphData: GraphData | null;
  width: number;
  height: number;
  selectedCohorts: number;
  nodeIdMap: NodeIdMapping;
  setNodeContainer: (container: PIXI.Container | null) => void;
  setLinkContainer: (container: PIXI.Container | null) => void;
  setHiddenContainer: (container: PIXI.Container | null) => void;
  onPixiCreated: (app: PIXI.Application) => void;
}
