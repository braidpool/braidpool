export interface BlockchainInfo {
  chain: string;
  blocks: number;
  headers: number;
  bestblockhash: string;
  difficulty: number;
  verificationprogress: number;
  chainwork: string;
  size_on_disk: number;
  pruned: boolean;
  warnings: string;
}

export interface PeerInfo {
  id: number;
  addr: string;
  version: number;
  subver: string;
  inbound: boolean;
  startingheight: number;
  synced_headers: number;
  synced_blocks: number;
  ping: number;
  bytessent: number;
  bytesrecv: number;
}

export interface NetworkInfo {
  version: number;
  subversion: string;
  protocolversion: number;
  localservices: string;
  localrelay: boolean;
  timeoffset: number;
  networkactive: boolean;
  connections: number;
  relayfee: number;
  incrementalfee: number;
  localaddresses: string[];
  warnings: string;
}
export interface Mempool {
  loaded: boolean;
  size: number;
  bytes: number;
  usage: number;
  maxmempool: number;
  mempoolminfee: number;
  minrelaytxfee: number;
}
export interface NetTotals {
  totalbytesrecv: number;
  totalbytessent: number;
  timemillis: number;
  uploadtarget: {
    timeframe: number;
    target: number;
    target_reached: boolean;
    serve_historical_blocks: boolean;
    bytes_left_in_cycle: number;
    time_left_in_cycle: number;
  };
}
export interface RawJsonViewerProps {
  data: object;
  title?: string;
}
