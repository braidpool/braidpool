/// <reference types="vite/client" />

interface ImportMetaEnv {
  readonly VITE_APP_TITLE: string;
  readonly VITE_NODE_RPC_WS?: string;
}

interface ImportMeta {
  readonly env: ImportMetaEnv;
}
