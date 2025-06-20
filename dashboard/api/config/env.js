import dotenv from 'dotenv';
dotenv.config();

export const PORT = process.env.PORT || 3001;
export const BRAIDPOOL_URL = process.env.BRAIDPOOL_URL;
export const RPC_USER = process.env.RPC_USER;
export const RPC_PASS = process.env.RPC_PASS;
