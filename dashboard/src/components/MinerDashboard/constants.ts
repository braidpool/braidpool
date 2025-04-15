import type { Miner, Transaction, TimeRange } from "./types"

export const TIME_RANGES: TimeRange[] = [
  { label: "Week", value: "week", days: 7 },
  { label: "Month", value: "month", days: 30 },
  { label: "Quarter", value: "quarter", days: 90 },
  { label: "Year", value: "year", days: 365 },
]

export const MINERS: Miner[] = [
  { id: "miner1", name: "miner1", timestamp: "2021-08-15 14:23", transactions: 31},
  { id: "miner2", name: "miner2", timestamp: "2021-08-30 09:17", transactions: 13 },
  { id: "miner3", name: "miner3", timestamp: "2021-09-05 11:42", transactions: 22 },
  { id: "miner4", name: "miner4", timestamp: "2021-09-12 16:08", transactions: 7 },
]

export const TRANSACTIONS: Record<string, Transaction[]> = {
  miner1: [
    { id: "tx1", hash: "f68b21db...de3b0803", timestamp: "2021-08-15 14:23", count: 12, blockId: "1243" },
    { id: "tx2", hash: "964aebde...4813c0a6", timestamp: "2021-08-15 14:33", count: 7, blockId: "1244" },
    { id: "tx3", hash: "2c1a7f84...477aec04", timestamp: "2021-08-30 09:17", count: 12, blockId: "1245" },
  ],
  miner2: [
    { id: "tx4", hash: "a7c43e9b...12f5d78c", timestamp: "2021-08-30 09:17", count: 9, blockId: "1246" },
    { id: "tx5", hash: "58d2f1ac...9e7b3d45", timestamp: "2021-08-30 10:05", count: 5, blockId: "1247" },
  ],
  miner3: [
    { id: "tx6", hash: "b9e72d1c...5a8f3e6b", timestamp: "2021-09-05 11:42", count: 14, blockId: "1248" },
    { id: "tx7", hash: "3f6a9c8d...2b7e4d1a", timestamp: "2021-09-05 12:15", count: 8, blockId: "1249" },
  ],
  miner4: [{ id: "tx8", hash: "c5d8e7f6...1a2b3c4d", timestamp: "2021-09-12 16:08", count: 7, blockId: "1250" }],
}

export const BLOCKS = [
  { id: "1243", miner: "miner1", timestamp: "2021-08-15 14:23", transactions: 12 },
  { id: "1244", miner: "miner1", timestamp: "2021-08-15 14:33", transactions: 7 },
  { id: "1245", miner: "miner1", timestamp: "2021-08-30 09:17", transactions: 12 },
  { id: "1246", miner: "miner2", timestamp: "2021-08-30 09:17", transactions: 9 },
  { id: "1247", miner: "miner2", timestamp: "2021-08-30 10:05", transactions: 5 },
  { id: "1248", miner: "miner3", timestamp: "2021-09-05 11:42", transactions: 14 },
  { id: "1249", miner: "miner3", timestamp: "2021-09-05 12:15", transactions: 8 },
  { id: "1250", miner: "miner4", timestamp: "2021-09-12 16:08", transactions: 7 },
]