import axios from 'axios';

const TIMEOUT = 10000;
const MAX_RETRIES = 2;
const delay = (ms) => new Promise((res) => setTimeout(res, ms));
let requestId = 0;

async function rpcCall(method, params = [], retries = MAX_RETRIES) {
  const url = process.env.BRAIDPOOL_NODE_URL;

  if (!url) {
    throw new Error('BRAIDPOOL_NODE_URL not set');
  }

  try {
    const response = await axios.post(
      url,
      {
        jsonrpc: '2.0',
        id: ++requestId,
        method,
        params,
      },
      {
        headers: { 'Content-Type': 'application/json' },
        timeout: TIMEOUT,
      }
    );

    if (response.data.error) {
      throw new Error(JSON.stringify(response.data.error));
    }

    return response.data.result;
  } catch (error) {
    if (retries > 0) {
      console.warn(`Retrying ${method}...`);
      await delay(1000);
      return rpcCall(method, params, retries - 1);
    }
    throw error;
  }
}

const getPeerInfo = () => rpcCall('getpeerinfo');
const getBraidInfo = () => rpcCall('getbraidinfo');
const getHighestWorkPathByCount = (count = 50) =>
  rpcCall('gethighestworkpathbycount', [count]);
const getCohortById = (id) => rpcCall('getcohortbyid', [id]);
const getParents = (hash) => rpcCall('getparents', [hash]);

async function fetchDAGData(cohortCount, numCohorts = 10) {
  const startCohort = Math.max(0, cohortCount - numCohorts);

  const cohortPromises = [];
  for (let i = startCohort; i < cohortCount; i++) {
    cohortPromises.push(
      getCohortById(i).catch((err) => {
        console.warn(`Failed to fetch cohort ${i}:`, err.message);
        return [];
      })
    );
  }
  const cohorts = await Promise.all(cohortPromises);

  const allBeads = cohorts.flat();

  const parentPromises = allBeads.map((hash) =>
    getParents(hash)
      .then((parents) => [hash, parents])
      .catch(() => [hash, []])
  );
  const parentPairs = await Promise.all(parentPromises);
  const parents = Object.fromEntries(parentPairs);

  const children = {};
  for (const [nodeId, parentList] of Object.entries(parents)) {
    for (const parentId of parentList) {
      if (!children[parentId]) {
        children[parentId] = [];
      }
      children[parentId].push(nodeId);
    }
  }

  return { cohorts, parents, children };
}

export async function fetchBraidpoolBeadInfo() {
  const [braidInfoResult, peerInfoResult, hwpResult] = await Promise.allSettled(
    [getBraidInfo(), getPeerInfo(), getHighestWorkPathByCount(50)]
  );

  const braidInfo =
    braidInfoResult.status === 'fulfilled' ? braidInfoResult.value : null;
  const cohortCount = braidInfo?.cohort_count ?? 0;

  const data = {
    braidInfo,
    peerInfo:
      peerInfoResult.status === 'fulfilled' ? peerInfoResult.value : null,
    highestWorkPath: hwpResult.status === 'fulfilled' ? hwpResult.value : [],
    cohorts: [],
    parents: {},
    children: {},
  };

  if (cohortCount > 0) {
    try {
      const dagData = await fetchDAGData(cohortCount, 10);
      data.cohorts = dagData.cohorts;
      data.parents = dagData.parents;
      data.children = dagData.children;
    } catch (err) {
      console.warn('Failed to fetch DAG data:', err.message);
    }
  }

  return data;
}
