import {
  BraidPoolTransaction,
  TransactionCategory,
<<<<<<< HEAD
} from "../components/Transactions/type";
import { BraidPoolApiConfig, ApiTransaction, ApiMempoolInfo } from "./types";
=======
} from '../types/transaction';
>>>>>>> 98366da (changes & formatting)

export type { BraidPoolApiConfig };

const defaultConfig: BraidPoolApiConfig = {
  baseUrl: import.meta.env.VITE_BRAIDPOOL_API_URL || "http://localhost:3000",
  timeout: 10000,
  retries: 3,
};

class BraidPoolApiError extends Error {
  constructor(
    message: string,
    public statusCode?: number,
    public response?: any,
  ) {
    super(message);
    this.name = "BraidPoolApiError";
  }
}

class BraidPoolApi {
  private config: BraidPoolApiConfig;

  constructor(config: Partial<BraidPoolApiConfig> = {}) {
    this.config = { ...defaultConfig, ...config };
  }

  private async makeRequest<T>(
    endpoint: string,
<<<<<<< HEAD
    options: RequestInit = {},
=======
    options: RequestInit = {}
>>>>>>> 98366da (changes & formatting)
  ): Promise<T> {
    const url = `${this.config.baseUrl}${endpoint}`;
    const controller = new AbortController();
    const timeoutId = setTimeout(() => controller.abort(), this.config.timeout);

    try {
      const response = await fetch(url, {
        ...options,
        signal: controller.signal,
        headers: {
<<<<<<< HEAD
          "Content-Type": "application/json",
          Accept: "application/json",
=======
          'Content-Type': 'application/json',
          Accept: 'application/json',
>>>>>>> 98366da (changes & formatting)
          ...options.headers,
        },
      });

      clearTimeout(timeoutId);

      if (!response.ok) {
        let errorMessage = `HTTP ${response.status}: ${response.statusText}`;
        try {
          const errorBody = await response.text();
          if (errorBody) errorMessage += ` - ${errorBody}`;
        } catch {}
        throw new BraidPoolApiError(errorMessage, response.status);
      }

      return await response.json();
    } catch (error: any) {
      clearTimeout(timeoutId);
      if (error instanceof BraidPoolApiError) throw error;
<<<<<<< HEAD
      if (error.name === "AbortError")
        throw new BraidPoolApiError("Request timeout");
      throw new BraidPoolApiError(
        error.message || "Unknown API error",
        undefined,
        error,
=======
      if (error.name === 'AbortError')
        throw new BraidPoolApiError('Request timeout');
      throw new BraidPoolApiError(
        error.message || 'Unknown API error',
        undefined,
        error
>>>>>>> 98366da (changes & formatting)
      );
    }
  }

  private async retryRequest<T>(
    endpoint: string,
<<<<<<< HEAD
    options: RequestInit = {},
=======
    options: RequestInit = {}
>>>>>>> 98366da (changes & formatting)
  ): Promise<T> {
    let lastError: Error;
    for (let attempt = 0; attempt <= this.config.retries; attempt++) {
      try {
        console.log(
<<<<<<< HEAD
          `🔄 BraidPool API Attempt ${attempt + 1}/${this.config.retries + 1}: ${endpoint}`,
=======
          `🔄 BraidPool API Attempt ${attempt + 1}/${this.config.retries + 1}: ${endpoint}`
>>>>>>> 98366da (changes & formatting)
        );
        const result = await this.makeRequest<T>(endpoint, options);
        console.log(`✅ BraidPool API Success: ${endpoint}`);
        return result;
      } catch (error: any) {
        lastError = error;
        console.warn(
          `❌ BraidPool API Attempt ${attempt + 1} failed for ${endpoint}:`,
<<<<<<< HEAD
          error.message,
=======
          error.message
>>>>>>> 98366da (changes & formatting)
        );
        if (attempt < this.config.retries) {
          const delay = Math.pow(2, attempt) * 1000;
          await new Promise((resolve) => setTimeout(resolve, delay));
        }
      }
    }
    console.error(`💥 All BraidPool API attempts failed for ${endpoint}`);
    throw lastError!;
  }

  async fetchRecentTransactions(
<<<<<<< HEAD
    limit: number = 10,
  ): Promise<BraidPoolTransaction[]> {
    const transactions =
      await this.retryRequest<ApiTransaction[]>("/transactions");
=======
    limit: number = 10
  ): Promise<BraidPoolTransaction[]> {
    const transactions =
      await this.retryRequest<ApiTransaction[]>('/transactions');
>>>>>>> 98366da (changes & formatting)
    return transactions
      .slice(0, limit)
      .map((tx) => this.transformToBraidPoolTransaction(tx));
  }

  async fetchMempoolInfo(): Promise<ApiMempoolInfo> {
    return await this.retryRequest<ApiMempoolInfo>("/mempool/info");
  }

  private normalizeCategory(category?: string): TransactionCategory {
    if (!category) return TransactionCategory.MEMPOOL;

    const normalized = category.trim().toLowerCase();

    // Exact match mapping
    const categoryMap: Record<string, TransactionCategory> = {
      confirmed: TransactionCategory.CONFIRMED,
      scheduled: TransactionCategory.SCHEDULED,
      proposed: TransactionCategory.PROPOSED,
      committed: TransactionCategory.COMMITTED,
      mempool: TransactionCategory.MEMPOOL,
      replaced: TransactionCategory.REPLACED,
      unconfirmed: TransactionCategory.MEMPOOL, // Explicitly handle unconfirmed
    };

    return categoryMap[normalized] || TransactionCategory.MEMPOOL;
  }

  private parseWork(work: string | number | null | undefined): {
    work: number;
    unit: string;
  } {
<<<<<<< HEAD
    if (work === null || work === undefined) return { work: 0, unit: "TH" };
    if (typeof work === "number") return { work, unit: "TH" };
=======
    if (work === null || work === undefined) return { work: 0, unit: 'TH' };
    if (typeof work === 'number') return { work, unit: 'TH' };
>>>>>>> 98366da (changes & formatting)
    const match = work.toString().match(/([\d.]+)\s*([TPE]H)?/i);
    if (!match) return { work: 0, unit: "TH" };
    const value = parseFloat(match[1]);
    const unit = (match[2] || "TH").toUpperCase();
    return { work: value, unit };
  }

  private transformToBraidPoolTransaction(
<<<<<<< HEAD
    tx: ApiTransaction,
=======
    tx: ApiTransaction
>>>>>>> 98366da (changes & formatting)
  ): BraidPoolTransaction {
    const { work, unit } = this.parseWork(tx.work);
    return {
      txid: tx.txid,
      hash: tx.hash || tx.txid,
      category: this.normalizeCategory(tx.category),
      size: tx.size || 0,
      weight: tx.weight || 0,
      fee: tx.fee || 0,
      feeRate: tx.fee_rate || 0,
      inputs: tx.inputs || 0,
      outputs: tx.outputs || 0,
      confirmations: tx.confirmations || 0,
      work,
      workUnit: tx.work_unit || unit,
      vin: tx.vin || [],
      vout: tx.vout || [],
      status: tx.status || { confirmed: (tx.confirmations || 0) > 0 },
      timestamp: tx.timestamp || Math.floor(Date.now() / 1000),
      rbfSignaled: !!tx.rbf_signaled,
    };
  }
}

export default BraidPoolApi;
export const braidpoolApi = new BraidPoolApi();
export { BraidPoolApiError };
