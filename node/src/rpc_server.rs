use crate::bead::Bead;
#[cfg(test)]
use crate::braid;
use crate::braid::AddBeadStatus;
use crate::braid::Braid;
use crate::error::BraidRPCError;
#[cfg(test)]
use crate::utils::create_test_bead;
use crate::utils::BeadHash;
use clap::Subcommand;
use jsonrpsee::core::async_trait;
use jsonrpsee::core::client::ClientT;
use jsonrpsee::core::middleware::Batch;
use jsonrpsee::core::middleware::Notification;
use jsonrpsee::core::middleware::RpcServiceT;
use jsonrpsee::core::params::ArrayParams;
use jsonrpsee::http_client::HttpClient;
use jsonrpsee::proc_macros::rpc;
use jsonrpsee::types::ErrorObjectOwned;
use jsonrpsee::types::Request;
use jsonrpsee::ConnectionId;
use log;
use serde_json;
use std::future::Future;
use std::net::SocketAddr;
use std::sync::Arc;
use tokio::sync::RwLock;

//Rpc commands
#[derive(Subcommand, Debug, Clone)]
pub enum RpcCommand {
    /// Get a bead by hash
    GetBead {
        /// The bead hash (as a hex string)
        bead_hash: String,
    },

    /// Add a bead via serialized JSON string
    AddBead {
        /// JSON-formatted bead
        bead_data: String,
    },

    /// Get total number of beads
    GetBeadCount,

    /// Get total number of cohorts
    GetCohortCount,

    /// Get current DAG tips
    GetTips,
}
//parsing the inital rpc command line all
pub async fn parse_arguments(cli_command: RpcCommand, server_addr: SocketAddr) -> () {
    // //initializing a client associated with the current node
    // //for receving the response from the server
    let target_uri = format!("http://{}", server_addr.to_string());
    let client_res: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    let (rpc_method, method_params) = match cli_command {
        RpcCommand::AddBead { bead_data } => {
            let rpc_method = String::from("addbead");
            let mut method_params = ArrayParams::new();
            method_params.insert(bead_data).unwrap();

            (rpc_method, method_params)
        }
        RpcCommand::GetBead { bead_hash } => {
            let rpc_method = "getbead".to_string();
            let mut method_params = ArrayParams::new();
            method_params.insert(bead_hash).unwrap();

            (rpc_method, method_params)
        }
        RpcCommand::GetBeadCount => {
            let rpc_method = String::from("getbeadcount");
            let method_params = ArrayParams::new();

            (rpc_method, method_params)
        }
        RpcCommand::GetCohortCount => {
            let method_params = ArrayParams::new();
            let rpc_method = String::from("getcohortcount");

            (rpc_method, method_params)
        }
        RpcCommand::GetTips => {
            let method_params = ArrayParams::new();
            let rpc_method = String::from("gettips");

            (rpc_method, method_params)
        }
    };
    tokio::spawn(handle_request(
        rpc_method.clone(),
        method_params,
        client_res,
    ));
}

//handling the request arising either from command line cli or from the external users
pub async fn handle_request(
    method: String,
    method_params: ArrayParams,
    client: HttpClient,
) -> Result<(), BraidRPCError> {
    let rpc_response: Result<String, jsonrpsee::core::ClientError> =
        client.request(&method, method_params.clone()).await;
    match rpc_response {
        Ok(response) => {
            log::info!(
                "Response received successfully from the RPC server - {:?}",
                response
            );
            Ok(())
        }
        Err(error) => {
            log::error!(
                "An error occurred while receiving response from Server - {:?}",
                error
            );
            Err(BraidRPCError::RequestFailed {
                method: method,
                source: error,
            })
        }
    }
}

//server side trait to be implemented for the handler
//that is the JSON-RPC handle to initiate the RPC context
//supporting both http and websockets
#[rpc(server)]
pub trait Rpc {
    //RPC methods supported by braid-API
    #[method(name = "getbead")]
    async fn get_bead(&self, bead_hash: String) -> Result<String, ErrorObjectOwned>;

    #[method(name = "addbead")]
    async fn add_bead(&self, bead_data: String) -> Result<String, ErrorObjectOwned>;

    #[method(name = "gettips")]
    async fn get_tips(&self) -> Result<String, ErrorObjectOwned>;

    #[method(name = "getbeadcount")]
    async fn get_bead_count(&self) -> Result<String, ErrorObjectOwned>;

    #[method(name = "getcohortcount")]
    async fn get_cohort_count(&self) -> Result<String, ErrorObjectOwned>;
}

// RPC Server implementation using channels
pub struct RpcServerImpl {
    braid_arc: Arc<RwLock<Braid>>,
}

impl RpcServerImpl {
    pub fn new(braid_shared_pointer: Arc<RwLock<Braid>>) -> Self {
        Self {
            braid_arc: braid_shared_pointer,
        }
    }
}
#[async_trait]
impl RpcServer for RpcServerImpl {
    async fn get_bead(&self, bead_hash: String) -> Result<String, ErrorObjectOwned> {
        let hash = bead_hash
            .parse::<BeadHash>()
            .map_err(|_| ErrorObjectOwned::owned(1, "Invalid bead hash format", None::<()>))?;
        log::info!("Get bead request recieved from client");
        let braid_data = self.braid_arc.read().await;
        let bead = braid_data
            .beads
            .iter()
            .find(|bead| bead.block_header.block_hash() == hash)
            .cloned();

        match bead {
            Some(bead) => {
                let json = serde_json::to_string(&bead)
                    .map_err(|_| ErrorObjectOwned::owned(2, "Internal error", None::<()>))
                    .unwrap();
                Ok(json)
            }
            None => Err(ErrorObjectOwned::owned(3, "Bead not found", None::<()>)),
        }
    }

    async fn add_bead(&self, bead_data: String) -> Result<String, ErrorObjectOwned> {
        let bead: Bead = serde_json::from_str(&bead_data).map_err(|e| {
            ErrorObjectOwned::owned(1, format!("Invalid bead data: {}", e), None::<()>)
        })?;
        log::info!("Add bead request recieved from client");
        let mut braid_data = self.braid_arc.write().await;
        let success_status = braid_data.extend(&bead);

        match success_status {
            AddBeadStatus::BeadAdded => Ok("Bead added successfully".to_string()),
            AddBeadStatus::DagAlreadyContainsBead => Ok("Bead already exists".to_string()),
            AddBeadStatus::InvalidBead => {
                Err(ErrorObjectOwned::owned(4, "Invalid bead", None::<()>))
            }
            AddBeadStatus::ParentsNotYetReceived => {
                Ok("Bead queued, waiting for parents".to_string())
            }
        }
    }

    async fn get_tips(&self) -> Result<String, ErrorObjectOwned> {
        let braid_data = self.braid_arc.read().await;
        let tips: Vec<BeadHash> = braid_data
            .tips
            .iter()
            .map(|&index| braid_data.beads[index].block_header.block_hash())
            .collect();
        log::info!("Get tips request received from client");
        let tips_str: Vec<String> = tips.iter().map(|h| h.to_string()).collect();

        serde_json::to_string(&tips_str)
            .map_err(|_| ErrorObjectOwned::owned(2, "Internal error", None::<()>))
    }

    async fn get_bead_count(&self) -> Result<String, ErrorObjectOwned> {
        let braid_data = self.braid_arc.read().await;
        let count = braid_data.beads.len();
        log::info!("Get bead count request received  from client");
        Ok(count.to_string())
    }

    async fn get_cohort_count(&self) -> Result<String, ErrorObjectOwned> {
        let braid_data = self.braid_arc.read().await;
        log::info!("Get cohort request received from client ");
        let count = braid_data.cohorts.len();

        Ok(count.to_string())
    }
}
struct LoggingMiddleware<S>(S);

impl<S> RpcServiceT for LoggingMiddleware<S>
where
    S: RpcServiceT,
{
    type MethodResponse = S::MethodResponse;
    type NotificationResponse = S::NotificationResponse;
    type BatchResponse = S::BatchResponse;

    fn call<'a>(
        &self,
        request: Request<'a>,
    ) -> impl Future<Output = Self::MethodResponse> + Send + 'a {
        tracing::info!("Received request: {:?}", request);
        assert!(request.extensions().get::<ConnectionId>().is_some());

        self.0.call(request)
    }

    fn batch<'a>(&self, batch: Batch<'a>) -> impl Future<Output = Self::BatchResponse> + Send + 'a {
        tracing::info!("Received batch: {:?}", batch);
        self.0.batch(batch)
    }

    fn notification<'a>(
        &self,
        n: Notification<'a>,
    ) -> impl Future<Output = Self::NotificationResponse> + Send + 'a {
        tracing::info!("Received notif: {:?}", n);
        self.0.notification(n)
    }
}
//server building
//running a server in seperate spawn event
pub async fn run_rpc_server(braid_shared_pointer: Arc<RwLock<Braid>>) -> Result<SocketAddr, ()> {
    //Initializing the middleware
    let rpc_middleware =
        jsonrpsee::server::middleware::rpc::RpcServiceBuilder::new().layer_fn(LoggingMiddleware);
    //building the context/server supporting the http transport and ws
    let server = jsonrpsee::server::Server::builder()
        .set_rpc_middleware(rpc_middleware)
        .build("127.0.0.1:6682")
        .await
        .unwrap();
    //listening address for incoming requests/connection
    let addr = server.local_addr().unwrap();
    //context for the served server
    let rpc_impl = RpcServerImpl::new(braid_shared_pointer);
    let handle = server.start(rpc_impl.into_rpc());
    log::info!(
        "RPC Server is listening at socket address http://{:?}",
        addr
    );
    tokio::spawn(
        //handling the stopping of the server
        handle.stopped(),
    );
    Ok(addr)
}

#[tokio::test]
pub async fn test_extend_rpc() {
    let test_bead1 = create_test_bead(1, None);
    let genesis_beads = vec![test_bead1.clone()];

    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(genesis_beads)));

    let _ = run_rpc_server(Arc::clone(&braid)).await.unwrap();

    let server_addr = "127.0.0.1:6682";
    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    let new_bead = create_test_bead(2, Some(test_bead1.block_header.block_hash()));
    let bead_json_str = serde_json::to_string(&new_bead).expect("Failed to serialize bead");

    let mut params = ArrayParams::new();
    params.insert(bead_json_str).unwrap();

    //Extending the bead
    let response: Result<String, jsonrpsee::core::ClientError> =
        client.request("addbead", params).await;

    assert_eq!(response.unwrap(), "Bead added successfully".to_string());

    let get_bead_params = ArrayParams::new();
    //Checking for the updated bead count after successful extension of braid
    let num_beads: Result<String, jsonrpsee::core::ClientError> =
        client.request("getbeadcount", get_bead_params).await;

    assert_eq!(num_beads.unwrap(), "2".to_string());
}

#[tokio::test]
pub async fn test_same_bead_extend() {
    let test_bead1 = create_test_bead(1, None);
    let genesis_beads = vec![test_bead1.clone()];

    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(genesis_beads)));

    //Initializing the test server
    let rpc_middleware =
        jsonrpsee::server::middleware::rpc::RpcServiceBuilder::new().layer_fn(LoggingMiddleware);
    let server = jsonrpsee::server::Server::builder()
        .set_rpc_middleware(rpc_middleware)
        .build("127.0.0.1:8889")
        .await
        .unwrap();
    let rpc_impl = RpcServerImpl::new(braid);
    let _handle = server.start(rpc_impl.into_rpc());

    let server_addr = "127.0.0.1:8889";
    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    let new_bead = create_test_bead(2, Some(test_bead1.block_header.block_hash()));

    let bead_json_str = serde_json::to_string(&new_bead).expect("Failed to serialize bead");

    let mut params = ArrayParams::new();
    params.insert(bead_json_str).unwrap();

    //Extending the bead
    let _response_original: Result<String, jsonrpsee::core::ClientError> =
        client.request("addbead", params.clone()).await;

    //Extending the same bead again bead
    let response_duplicate: Result<String, jsonrpsee::core::ClientError> =
        client.request("addbead", params).await;
    assert_eq!(
        response_duplicate.unwrap(),
        "Bead already exists".to_string()
    );
}
#[tokio::test]
pub async fn test_cohort_count_rpc() {
    let test_bead_1 = create_test_bead(1, None);
    let test_bead_2 = create_test_bead(2, Some(test_bead_1.block_header.block_hash()));
    let test_bead_3 = create_test_bead(3, Some(test_bead_2.block_header.block_hash()));
    let test_bead_4 = create_test_bead(2, Some(test_bead_3.block_header.block_hash()));

    let genesis_beads = vec![test_bead_1.clone()];

    let braid: Arc<RwLock<braid::Braid>> = Arc::new(RwLock::new(braid::Braid::new(genesis_beads)));
    //Initializing the test server
    let rpc_middleware =
        jsonrpsee::server::middleware::rpc::RpcServiceBuilder::new().layer_fn(LoggingMiddleware);
    let server = jsonrpsee::server::Server::builder()
        .set_rpc_middleware(rpc_middleware)
        .build("127.0.0.1:9000")
        .await
        .unwrap();
    let rpc_impl = RpcServerImpl::new(braid);
    let _handle = server.start(rpc_impl.into_rpc());

    let server_addr = "127.0.0.1:9000";
    let target_uri = format!("http://{}", server_addr);
    let client: HttpClient = HttpClient::builder().build(target_uri).unwrap();

    let test_bead_2_json_str =
        serde_json::to_string(&test_bead_2).expect("Failed to serialize bead");
    let test_bead_3_json_str =
        serde_json::to_string(&test_bead_3).expect("Failed to serialize bead");
    let test_bead_4_json_str =
        serde_json::to_string(&test_bead_4).expect("Failed to serialize bead");

    let mut params_test_bead_2 = ArrayParams::new();
    params_test_bead_2.insert(test_bead_2_json_str).unwrap();
    let mut params_test_bead_3 = ArrayParams::new();
    params_test_bead_3.insert(test_bead_3_json_str).unwrap();
    let mut params_test_bead_4 = ArrayParams::new();
    params_test_bead_4.insert(test_bead_4_json_str).unwrap();

    //Extending the bead
    let response_test_bead_2: Result<String, jsonrpsee::core::ClientError> =
        client.request("addbead", params_test_bead_2).await;
    assert_eq!(
        response_test_bead_2.unwrap(),
        "Bead added successfully".to_string()
    );

    let response_test_bead_3: Result<String, jsonrpsee::core::ClientError> =
        client.request("addbead", params_test_bead_3).await;
    assert_eq!(
        response_test_bead_3.unwrap(),
        "Bead added successfully".to_string()
    );

    let response_test_bead_4: Result<String, jsonrpsee::core::ClientError> =
        client.request("addbead", params_test_bead_4).await;
    assert_eq!(
        response_test_bead_4.unwrap(),
        "Bead added successfully".to_string()
    );
    let response_cohort_cnt: Result<String, jsonrpsee::core::ClientError> =
        client.request("getcohortcount", ArrayParams::new()).await;

    assert_eq!(response_cohort_cnt.unwrap(), "4".to_string());
}
