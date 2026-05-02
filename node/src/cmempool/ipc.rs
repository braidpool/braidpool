use std::path::{Path, PathBuf};
use tokio::io::{AsyncReadExt, AsyncWriteExt};
use tokio::net::UnixStream;

use serde::{Deserialize, Serialize};
use serde_json::Value;

const MAX_RESPONSE_BYTES: u32 = 16 * 1024 * 1024;

#[derive(Debug, Serialize)]
struct IpcRequest<'a> {
    pub method: &'a str,
    pub params: Value,
}

#[derive(Debug, Deserialize)]
pub struct IpcResponse {
    pub result: Option<Value>,
    pub error: Option<IpcError>,
}

#[derive(Debug, Deserialize)]
pub struct IpcError {
    pub code: i64,
    pub message: String,
}

pub struct IpcClient {
    socket_path: PathBuf,
}

impl IpcClient {
    pub fn new<P: AsRef<Path>>(socket_path: P) -> Self {
        IpcClient {
            socket_path: socket_path.as_ref().to_path_buf(),
        }
    }

    async fn call(&self, method: &str, params: Value) -> Result<IpcResponse, IpcClientError> {
        let mut stream = UnixStream::connect(&self.socket_path)
            .await
            .map_err(|e| IpcClientError::Connect(self.socket_path.clone(), e))?;

        let request = IpcRequest { method, params };
        let body = serde_json::to_vec(&request).map_err(IpcClientError::Serialize)?;

        let len = u32::try_from(body.len()).map_err(|_| IpcClientError::RequestTooLarge)?;
        stream.write_all(&len.to_le_bytes()).await.map_err(IpcClientError::Write)?;
        stream.write_all(&body).await.map_err(IpcClientError::Write)?;

        let mut len_buf = [0u8; 4];
        stream.read_exact(&mut len_buf).await.map_err(IpcClientError::Read)?;
        let resp_len = u32::from_le_bytes(len_buf);

        if resp_len > MAX_RESPONSE_BYTES {
            return Err(IpcClientError::ResponseTooLarge(resp_len));
        }

        let mut resp_buf = vec![0u8; resp_len as usize];
        stream.read_exact(&mut resp_buf).await.map_err(IpcClientError::Read)?;

        serde_json::from_slice(&resp_buf).map_err(IpcClientError::Deserialize)
    }

    pub async fn get_block_template(&self, reserved_weight: u64) -> Result<Value, IpcClientError> {
        let params = serde_json::json!([{
            "rules": ["segwit"],
            "reserved_weight": reserved_weight,
        }]);
        let resp = self.call("getblocktemplate", params).await?;
        resp.result.ok_or_else(|| {
            let msg = resp
                .error
                .map(|e| e.message)
                .unwrap_or_else(|| "empty result".to_string());
            IpcClientError::RpcError(msg)
        })
    }

    pub async fn send_raw_transaction(&self, raw_tx_hex: &str) -> Result<bool, IpcClientError> {
        let params = serde_json::json!([raw_tx_hex]);
        let resp = self.call("sendrawtransaction", params).await?;
        Ok(resp.error.is_none())
    }

    pub async fn notify_new_block(&self, block_hex: &str) -> Result<(), IpcClientError> {
        let params = serde_json::json!([block_hex]);
        let resp = self.call("submitblock", params).await?;
        if let Some(err) = resp.error {
            return Err(IpcClientError::RpcError(err.message));
        }
        Ok(())
    }
}

#[derive(Debug)]
pub enum IpcClientError {
    Connect(PathBuf, std::io::Error),
    Write(std::io::Error),
    Read(std::io::Error),
    Serialize(serde_json::Error),
    Deserialize(serde_json::Error),
    RequestTooLarge,
    ResponseTooLarge(u32),
    RpcError(String),
}

impl std::fmt::Display for IpcClientError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IpcClientError::Connect(p, e) => write!(f, "failed to connect to cmempoold at {}: {}", p.display(), e),
            IpcClientError::Write(e) => write!(f, "IPC write error: {}", e),
            IpcClientError::Read(e) => write!(f, "IPC read error: {}", e),
            IpcClientError::Serialize(e) => write!(f, "request serialization failed: {}", e),
            IpcClientError::Deserialize(e) => write!(f, "response deserialization failed: {}", e),
            IpcClientError::RequestTooLarge => write!(f, "IPC request body exceeds u32"),
            IpcClientError::ResponseTooLarge(n) => write!(f, "cmempoold response too large: {} bytes", n),
            IpcClientError::RpcError(msg) => write!(f, "cmempoold RPC error: {}", msg),
        }
    }
}

impl std::error::Error for IpcClientError {}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn ipc_request_serializes_correctly() {
        let req = IpcRequest {
            method: "getblocktemplate",
            params: json!([{"rules": ["segwit"]}]),
        };
        let s = serde_json::to_string(&req).unwrap();
        assert!(s.contains("\"method\":\"getblocktemplate\""));
        assert!(s.contains("\"params\""));
    }

    #[test]
    fn ipc_response_ok_deserializes() {
        let raw = r#"{"result": "000000abcdef", "error": null}"#;
        let resp: IpcResponse = serde_json::from_str(raw).unwrap();
        assert!(resp.result.is_some());
        assert!(resp.error.is_none());
    }

    #[test]
    fn ipc_response_error_deserializes() {
        let raw = r#"{"result": null, "error": {"code": -22, "message": "TX decode failed"}}"#;
        let resp: IpcResponse = serde_json::from_str(raw).unwrap();
        assert!(resp.result.is_none());
        let err = resp.error.unwrap();
        assert_eq!(err.code, -22);
        assert_eq!(err.message, "TX decode failed");
    }

    #[test]
    fn ipc_client_error_display() {
        let e = IpcClientError::RpcError("bad tx".to_string());
        assert_eq!(format!("{}", e), "cmempoold RPC error: bad tx");
    }
}
