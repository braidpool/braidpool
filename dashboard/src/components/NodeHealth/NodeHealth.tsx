// src/components/NodeHealth/NodeHealth.tsx
import React, { useState,useEffect } from 'react';
import { getBlockchainInfo,getPeerInfo, getNetworkInfo,getMempoolInfo,getNetTotals} from "./__tests__/nodeApi";
import { BlockchainInfo } from './__tests__/types';
import Peers from "./Peers";
import NetworkPanel from "./Network";
import MempoolPanel from "./Mempool";
import BandwidthPanel from "./Bandwidth";
import RawJsonViewer from "./Rawdatajson";
const TABS = [
  { label: "Blockchain", value: "blockchain" },
  { label: "Peers", value: "peers" },
  { label: "Network", value: "network" },
  { label: "Mempool", value: "mempool" },
  { label: "Bandwidth", value: "bandwidth" },
];
const NodeHealth: React.FC = () => {
   const [activeTab, setActiveTab] = useState("blockchain");
    const [blockchainInfo, setBlockchainInfo] = useState<any>(null);
    const [peerInfo, setPeerInfo] = useState<any[]>([]);
    const [networkInfo, setNetworkInfo] = useState<any>(null);
    const [mempoolInfo, setMempoolInfo] = useState<any>(null);
    const [netTotals, setNetTotals] = useState<any>(null);
    const [lastUpdated, setLastUpdated] = useState<string>(new Date().toLocaleTimeString());
    const [loading, setLoading] = useState<boolean>(true);
    const [error, setError] = useState<string | null>(null)
  const [blockInfo, setBlockInfo] = useState<BlockchainInfo | null>(null);
  
  const fetchAllData = async () => {
    try {
      setLoading(true);
      const [blockchain,peers,network,mempool,totals] = await await Promise.all([
              getBlockchainInfo(),
              getPeerInfo(),
              getNetworkInfo(),
              getMempoolInfo(),
              getNetTotals()
            ]);setBlockchainInfo(blockchain);
      setPeerInfo(peers);
      setNetworkInfo(network);
      setMempoolInfo(mempool);
      setNetTotals(totals);
      setLastUpdated(new Date().toLocaleTimeString());
      setError(null);
    } catch (err) {
      console.error("Error fetching blockchain info:", err);
      setError("Failed to fetch block height. Check proxy or cookie.");
    } finally {
      setLoading(false);
    }
  };
   useEffect(() => {
       fetchAllData();
       
       // Set up auto-refresh every 30 seconds
       const interval = setInterval(fetchAllData, 30000);
       return () => clearInterval(interval);
     }, []);
   
     if (loading && !blockchainInfo) {
       return <div className="min-h-screen bg-black text-white flex items-center justify-center">Loading...</div>;
     }
   
     if (error) {
       return (
         <div className="min-h-screen bg-black text-white flex items-center justify-center">
           <div className="text-center">
             <p className="text-red-500 mb-4">{error}</p>
             <button 
               onClick={fetchAllData}
               className="bg-white text-black px-4 py-2 rounded"
             >
               Retry
             </button>
           </div>
         </div>
       );
     }
      

  return (
     <div className="min-h-screen bg-black px-2 sm:px-4 md:px-6 py-6 md:py-8 text-black">
          <div className="mb-4 flex flex-row md:flex-row items-start md:items-center justify-between gap-4 bg-[#1c1c1c] px-4 py-3 rounded-3xl">
            <h1 className="text-2xl md:text-3xl font-bold text-white">
              Node Health Dashboard
              <p className="text-xs sm:text-sm text-gray-500 ">Last updated: 10:44:54 AM</p>
            </h1>
            <div className="flex items-center mt-3 gap-4">
              <span className="bg-green-100 text-green-700 px-3 py-1 rounded-full text-xs font-medium">
                Auto-refresh ON
              </span>
              <button className="rounded-md border text-white border-gray-300 px-4 py-1 text-sm hover:bg-gray-100 hover:text-black">
                Refresh
              </button>
            </div>
          </div>
    
          {/* Top Summary Cards */}
          <div className="grid grid-cols-4 sm:grid-cols-2 lg:grid-cols-4 gap-4 md:gap-6">
            {/* Sync Status */}
            <div className="bg-[#1c1c1c] border border-gray-700 rounded-xl backdrop-blur-sm shadow-md px-2 py-2">
              <h2 className="text-xs sm:text-sm text-gray-500 mb-1">Sync Status</h2>
               <p className={`text-lg sm:text-xl font-bold mb-1 ${blockchainInfo.headers === blockchainInfo.blocks ? "text-green-600" : "text-yellow-500"}`}>
      {blockchainInfo.headers === blockchainInfo.blocks ? "Synced" : "Syncing"}
    </p>
              <div className="w-full h-4 rounded text-white bg-gray-200">
                <div
        className="h-full rounded bg-black"
        style={{
          width: `${((blockchainInfo.blocks / blockchainInfo.headers) * 100).toFixed(2)}%`
        }}
      ></div>
              </div>
              <p className="text-xs text-gray-500 mt-1"> {((blockchainInfo.blocks / blockchainInfo.headers) * 100).toFixed(2)}% complete
    </p>
            </div>
    
            {/* Block Height */}
            <div className="bg-[#1c1c1c] border border-gray-700 rounded-xl backdrop-blur-sm shadow-md px-2 py-2">
              <h2 className="text-xs sm:text-sm text-gray-500 mb-1">Block Height</h2>
              <p className="text-lg sm:text-xl text-gray-500 font-bold">{blockchainInfo.blocks}</p>
              <p className="text-xs text-gray-500">{(blockchainInfo.size_on_disk/(1024*1024*1024)).toFixed(2)}GB</p>
            </div>
    
            {/* Connections */}
            <div className="bg-[#1c1c1c] border border-gray-700 rounded-xl backdrop-blur-sm shadow-md px-2 py-2">
              <h2 className="text-xs sm:text-sm text-gray-500 mb-1">Connections</h2>
              <p className="text-lg sm:text-xl text-white font-bold">{networkInfo.connections ?? "..."}</p>
              <p className="text-xs text-gray-500">{networkInfo
        ? `${networkInfo.connections_in ?? "?"} inbound, ${networkInfo.connections_out ?? "?"} outbound`
        : ""}</p>
            </div>
    
            {/* Mempool */}
            <div className="bg-[#1c1c1c] border border-gray-700 rounded-xl backdrop-blur-sm shadow-md px-2 py-2">
              <h2 className="text-xs sm:text-sm text-gray-500 mb-1">Mempool</h2>
              <p className="text-lg sm:text-xl font-bold">{mempoolInfo?.size?.toLocaleString() ?? "..."}</p>
              <div className="w-full h-4 rounded bg-gray-200">
                <div className="h-full  rounded bg-black" style={{
          width: mempoolInfo && mempoolInfo.bytes && mempoolInfo.maxmempool
            ? `${((mempoolInfo.bytes / mempoolInfo.maxmempool) * 100).toFixed(2)}%`
            : "0%"
        }}></div>
              </div>
              <p className="text-xs text-gray-500 mt-1">{mempoolInfo && mempoolInfo.bytes
        ? `${(mempoolInfo.bytes / (1024 * 1024)).toFixed(2)} MB`
        : "..."}</p>
            </div>
          </div>
    
          {/* Tabs */}
          <div className="mt-8 border border-gray-700 rounded-xl backdrop-blur-sm shadow-md overflow-x-auto bg-[#1c1c1c] p-3 flex items-center justify-center ">
            <nav className="flex gap-4 sm:gap-10 text-xs sm:text-sm font-medium whitespace-nowrap">
              {TABS.map((tab) => (
                <button
                  key={tab.value}
                  className={`py-2 border-b-2 ${
                    activeTab === tab.value
                      ? "text-white border-black"
                      : "text-gray-500 border-transparent"
                  }`}
                  onClick={() => setActiveTab(tab.value)}
                >
                  {tab.label}
                </button>
              ))}
            </nav>
          </div>
    
          {/* Tab Content */}
          <div className="mt-6">
  {activeTab === "blockchain" && blockchainInfo && (
    <div className="grid grid-cols-1 md:grid-cols-2 gap-4 md:gap-6 mt-6">
      <div className="rounded-xl border border-gray-700 backdrop-blur-sm shadow-md  p-4 md:p-6 bg-[#1c1c1c]">
        <h3 className="text-base md:text-lg flex items-center justify-center  text-white font-semibold mb-4">Blockchain Information</h3>
        <div className="space-y-2 text-xs sm:text-sm">
          <div className="flex justify-between">
            <span className="text-gray-500">Chain</span>
            <span className="font-medium text-white">{blockchainInfo.chain}</span>
          </div>
          <div className="flex justify-between"> 
            <span className="text-gray-500">Current Blocks</span>
            <span className="font-medium text-white">{blockchainInfo.blocks}</span>
          </div>
          <div className="flex justify-between"> 
            <span className="text-gray-500">Synced</span>
            <span className="font-medium text-white">{blockchainInfo.headers === blockchainInfo.blocks ? "True" : "False"}</span>
          </div>
          <div className="flex justify-between"> 
            <span className="text-gray-500">Blocks Best Hash</span>
            <span className="font-medium text-white">{blockchainInfo.bestblockhash}</span>
          </div>
          <div className="flex justify-between">
            <span className="text-gray-500">Verification Progress</span>
            <span className="text-white font-medium">{(blockchainInfo.verificationprogress * 100).toFixed(4)}%</span>
          </div>
          <div className="flex justify-between">
            <span className="text-gray-500">Difficulty</span>
            <span className="font-medium text-white">{blockchainInfo.difficulty}</span>
          </div>
          <div className="flex justify-between">
            <span className="text-gray-500">Pruned</span>
            <span className="bg-black text-white px-2 py-0.5 rounded-full text-xs">{blockchainInfo.pruned ? "True" : "False"}</span>
          </div>
          <div className="flex justify-between">
            <span className="text-gray-500">Warnings</span>
            <span className="font-medium text-white">{blockchainInfo.warnings || "None"}</span>
          </div>
        </div>
      </div>
      <RawJsonViewer data={blockchainInfo} />
    </div>
  )}

  {activeTab === "peers" && peerInfo && <Peers peers={peerInfo} />}
  {activeTab === "network" && networkInfo && <NetworkPanel network={networkInfo} />}
  {activeTab === "mempool" && mempoolInfo && <MempoolPanel mempool={mempoolInfo} />}
  {activeTab === "bandwidth" && netTotals && <BandwidthPanel nettotals={netTotals} />}
</div>
         
        </div>
      );
    };
    
    export default NodeHealth;