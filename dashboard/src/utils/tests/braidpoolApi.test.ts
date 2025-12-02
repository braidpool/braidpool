import { describe, it, expect, vi, beforeEach } from "vitest";
import BraidPoolApi, { BraidPoolApiError } from "../braidpoolApi";
import { TransactionCategory } from "@/components/Transactions/type";

global.fetch = vi.fn();

describe("BraidPoolApi - Basic Tests", () => {
  const mockFetch = global.fetch as any;

  beforeEach(() => {
    vi.clearAllMocks();
  });

  describe("Constructor", () => {
    it("creates instance with default config", () => {
      const api = new BraidPoolApi();
      expect(api).toBeInstanceOf(BraidPoolApi);
    });

    it("creates instance with custom config", () => {
      const api = new BraidPoolApi({
        baseUrl: "http://custom.com",
        timeout: 5000,
        retries: 2,
      });
      expect(api).toBeInstanceOf(BraidPoolApi);
    });
  });

  describe("fetchRecentTransactions", () => {
    it("returns array of transactions", async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => [
          {
            txid: "test123",
            confirmations: 0,
          },
        ],
      });

      const api = new BraidPoolApi();
      const result = await api.fetchRecentTransactions(1);

      expect(Array.isArray(result)).toBe(true);
      expect(result[0].txid).toBe("test123");
    });

    it("handles empty response", async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => [],
      });

      const api = new BraidPoolApi();
      const result = await api.fetchRecentTransactions(10);

      expect(result).toEqual([]);
    });
  });

  describe("Error Handling", () => {
    it("throws error on failed request", async () => {
      mockFetch.mockResolvedValueOnce({
        ok: false,
        status: 500,
        statusText: "Server Error",
        text: async () => "Error",
      });

      const api = new BraidPoolApi();

      await expect(api.fetchRecentTransactions(10)).rejects.toThrow(
        BraidPoolApiError,
      );
    }, 10000);
  });

  describe("Category Normalization", () => {
    it("normalizes confirmed category", async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => [
          {
            txid: "test",
            category: "confirmed",
            confirmations: 6,
          },
        ],
      });

      const api = new BraidPoolApi();
      const result = await api.fetchRecentTransactions(1);

      expect(result[0].category).toBe(TransactionCategory.CONFIRMED);
    });

    it("defaults unknown categories to mempool", async () => {
      mockFetch.mockResolvedValueOnce({
        ok: true,
        json: async () => [
          {
            txid: "test",
            category: "unknown",
            confirmations: 0,
          },
        ],
      });

      const api = new BraidPoolApi();
      const result = await api.fetchRecentTransactions(1);

      expect(result[0].category).toBe(TransactionCategory.MEMPOOL);
    });
  });
});
