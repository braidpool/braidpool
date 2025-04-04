import type { BraidData, NetworkStatsData, TransactionMetricsData } from "./types"

// Mock API functions for demonstration
// In a real implementation, these would connect to your Python Flask API

// Fetch braid data
export async function fetchBraidData(): Promise<BraidData> {
  // Simulate API call
  return new Promise((resolve) => {
    setTimeout(() => {
      resolve({
        beads: generateMockBeads(),
      })
    }, 500)
  })
}

// Fetch network stats
export async function fetchNetworkStats(): Promise<NetworkStatsData> {
  // Simulate API call
  return new Promise((resolve) => {
    setTimeout(() => {
      resolve({
        activeNodes: Math.floor(Math.random() * 1000) + 5000,
        nodeChange: Math.random() * 5 - 2.5,
        transactions: Math.floor(Math.random() * 10000) + 50000,
        transactionChange: Math.random() * 8 - 3,
        poolHashrate: Math.random() * 50 + 150,
        hashrateChange: Math.random() * 10 - 5,
        blocksMined: Math.floor(Math.random() * 20) + 100,
        blocksChange: Math.random() * 15 - 7,
      })
    }, 700)
  })
}

// Fetch transaction metrics
export async function fetchTransactionMetrics(): Promise<TransactionMetricsData> {
  // Simulate API call
  return new Promise((resolve) => {
    setTimeout(() => {
      const now = new Date()
      const transactionRateHistory = Array.from({ length: 24 }, (_, i) => {
        const date = new Date(now)
        date.setHours(date.getHours() - (23 - i))
        return {
          timestamp: date.toISOString(),
          value: Math.random() * 50 + 100,
        }
      })

      const confirmationTimeHistory = Array.from({ length: 24 }, (_, i) => {
        const date = new Date(now)
        date.setHours(date.getHours() - (23 - i))
        return {
          timestamp: date.toISOString(),
          value: Math.random() * 5 + 7,
        }
      })

      const feeDistribution = [
        { category: "0-5 sat/vB", count: Math.floor(Math.random() * 100) + 50 },
        { category: "5-10 sat/vB", count: Math.floor(Math.random() * 200) + 150 },
        { category: "10-20 sat/vB", count: Math.floor(Math.random() * 300) + 250 },
        { category: "20-50 sat/vB", count: Math.floor(Math.random() * 200) + 100 },
        { category: "50-100 sat/vB", count: Math.floor(Math.random() * 100) + 50 },
        { category: ">100 sat/vB", count: Math.floor(Math.random() * 50) + 20 },
      ]

      resolve({
        currentTransactionRate: Math.random() * 20 + 120,
        transactionRateHistory,
        currentConfirmationTime: Math.random() * 3 + 8,
        confirmationTimeHistory,
        averageFee: Math.random() * 0.0001 + 0.0002,
        feeDistribution,
      })
    }, 600)
  })
}

// Helper function to generate mock bead data
function generateMockBeads() {
  const beads = []
  const cohorts = 8 // Increased number of cohorts
  const beadsPerCohort = 6 // Increased beads per cohort

  // Generate blocks (one per cohort)
  for (let i = 0; i < cohorts; i++) {
    const blockId = `block${i + 1}`
    const isPoolMined = Math.random() > 0.3 // 70% chance of being pool-mined

    beads.push({
      id: blockId,
      cohort: i,
      isBlock: true,
      isHighestWorkPath: true,
      isPoolMined,
      parents: i > 0 ? [`block${i}`] : [],
      children: i < cohorts - 1 ? [`block${i + 2}`] : [],
    })
  }

  // Generate regular beads
  let beadCounter = 1
  for (let i = 0; i < cohorts; i++) {
    for (let j = 0; j < beadsPerCohort; j++) {
      const beadId = `bead${beadCounter++}`
      const isHighestWorkPath = Math.random() > 0.8 // 20% chance of being on highest work path

      // Determine parents
      const parents = []
      if (i > 0) {
        // Add block from previous cohort as parent with 50% probability
        if (Math.random() > 0.5) {
          parents.push(`block${i}`)
        }

        // Add 1-2 beads from previous cohort as parents
        const prevCohortBeads = beads.filter((b) => b.cohort === i - 1 && !b.isBlock)
        if (prevCohortBeads.length > 0) {
          const numParents = Math.floor(Math.random() * 2) + 1
          for (let k = 0; k < numParents && k < prevCohortBeads.length; k++) {
            const randomIndex = Math.floor(Math.random() * prevCohortBeads.length)
            const parentId = prevCohortBeads[randomIndex].id
            if (!parents.includes(parentId)) {
              parents.push(parentId)
            }
          }
        }
      }

      // If no parents were assigned and this isn't the first cohort, add the block as parent
      if (parents.length === 0 && i > 0) {
        parents.push(`block${i}`)
      }

      beads.push({
        id: beadId,
        cohort: i,
        isBlock: false,
        isHighestWorkPath,
        isPoolMined: true, // Regular beads are always pool-mined
        parents,
        children: [],
      })
    }
  }

  // Update children arrays
  beads.forEach((bead) => {
    bead.parents.forEach((parentId) => {
      const parent = beads.find((b) => b.id === parentId)
      if (parent && !parent.children.includes(bead.id)) {
        parent.children.push(bead.id)
      }
    })
  })

  return beads
}

