# Braidpool Node RPC API Documentation

This document describes all available RPC endpoints for the Braidpool node. The RPC API follows the JSON-RPC 2.0 specification and supports both HTTP and WebSocket transport.

## Server Configuration

- **Default Address**: `127.0.0.1:6682`
- **Protocol**: JSON-RPC 2.0
- **Transport**: HTTP, WebSocket

## Available Endpoints

### 1. `getbead`

Retrieves a specific bead by its hash.

**Parameters:**
- `bead_hash` (string): The bead hash as a hex string

**Returns:**
- JSON string containing the complete bead data

**Example:**
```bash
curl -X POST http://127.0.0.1:6682 \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc": "2.0", "method": "getbead", "params": ["1234567890abcdef..."], "id": 1}'
```

**Response:**
```json
{
  "jsonrpc": "2.0",
  "result": "{\"block_header\": {...}, \"committed_metadata\": {...}, \"uncommitted_metadata\": {...}}",
  "id": 1
}
```

**Error Codes:**
- **1**: Invalid bead hash format
- **2**: Internal error (JSON serialization failed)
- **3**: Bead not found

---

### 2. `addbead`

Adds a new bead to the braid.

**Parameters:**
- `bead_data` (string): JSON-formatted bead data

**Returns:**
- Status message string

**Example:**
```bash
curl -X POST http://127.0.0.1:6682 \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc": "2.0", "method": "addbead", "params": ["{\"block_header\": {...}}"], "id": 1}'
```

**Response:**
```json
{
  "jsonrpc": "2.0",
  "result": "Bead added successfully",
  "id": 1
}
```

**Possible Results:**
- `"Bead added successfully"`: Bead was successfully added to the braid
- `"Bead already exists"`: Bead was already present in the braid
- `"Bead queued, waiting for parents"`: Bead is valid but parents are not yet available

**Error Codes:**
- **1**: Invalid bead data format
- **4**: Invalid bead (validation failed)

---

### 3. `gettips`

Retrieves the current tip beads (leaves) of the braid DAG.

**Parameters:** None

**Returns:**
- JSON array of bead hashes (as strings)

**Example:**
```bash
curl -X POST http://127.0.0.1:6682 \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc": "2.0", "method": "gettips", "params": [], "id": 1}'
```

**Response:**
```json
{
  "jsonrpc": "2.0",
  "result": "[\"1234567890abcdef...\", \"fedcba0987654321...\"]",
  "id": 1
}
```

**Error Codes:**
- **2**: Internal error (JSON serialization failed)

---

### 4. `getgeneses`

Retrieves the genesis beads (root nodes with no parents) of the braid DAG.

**Parameters:** None

**Returns:**
- JSON array of bead hashes (as strings)

**Example:**
```bash
curl -X POST http://127.0.0.1:6682 \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc": "2.0", "method": "getgeneses", "params": [], "id": 1}'
```

**Response:**
```json
{
  "jsonrpc": "2.0",
  "result": "[\"abcdef1234567890...\", \"0987654321fedcba...\"]",
  "id": 1
}
```

**Error Codes:**
- **2**: Internal error (JSON serialization failed)

---

### 5. `getbeadcount`

Gets the total number of beads in the braid.

**Parameters:** None

**Returns:**
- String representation of the bead count

**Example:**
```bash
curl -X POST http://127.0.0.1:6682 \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc": "2.0", "method": "getbeadcount", "params": [], "id": 1}'
```

**Response:**
```json
{
  "jsonrpc": "2.0",
  "result": "42",
  "id": 1
}
```

**Error Codes:** None

---

### 6. `getcohortcount`

Gets the total number of cohorts in the braid.

**Parameters:** None

**Returns:**
- String representation of the cohort count

**Example:**
```bash
curl -X POST http://127.0.0.1:6682 \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc": "2.0", "method": "getcohortcount", "params": [], "id": 1}'
```

**Response:**
```json
{
  "jsonrpc": "2.0",
  "result": "15",
  "id": 1
}
```

**Error Codes:** None

---

### 7. `getbeadsincohort`

Retrieves beads from a specific cohort in the braid.

**Parameters:**
- `i` (number): The index from the end of the cohorts list
  - `0` = latest/most recent cohort (default)
  - `1` = second-to-last cohort
  - `2` = third-to-last cohort
  - etc.

**Returns:**
- JSON array of bead hashes (as strings) belonging to the specified cohort

**Example:**
```bash
# Get beads from latest cohort
curl -X POST http://127.0.0.1:6682 \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc": "2.0", "method": "getbeadsincohort", "params": [0], "id": 1}'

# Get beads from second-to-last cohort
curl -X POST http://127.0.0.1:6682 \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc": "2.0", "method": "getbeadsincohort", "params": [1], "id": 1}'
```

**Response:**
```json
{
  "jsonrpc": "2.0",
  "result": "[\"1234567890abcdef...\", \"fedcba0987654321...\"]",
  "id": 1
}
```

**Error Codes:**
- **2**: Internal error (JSON serialization failed)
- **5**: No cohorts available
- **6**: Cohort index out of bounds

---

## Command Line Interface

The node also supports these RPC methods through command line arguments:

```bash
# Get a specific bead
./node rpc get-bead --bead-hash "1234567890abcdef..."

# Add a bead
./node rpc add-bead --bead-data '{"block_header": {...}}'

# Get current tips
./node rpc get-tips

# Get genesis beads
./node rpc get-geneses

# Get bead count
./node rpc get-bead-count

# Get cohort count
./node rpc get-cohort-count

# Get beads in specific cohort
./node rpc get-beads-in-cohort --i 0  # Latest cohort
./node rpc get-beads-in-cohort --i 1  # Second-to-last cohort
```

## Error Handling

All RPC methods return standard JSON-RPC 2.0 error responses when something goes wrong:

```json
{
  "jsonrpc": "2.0",
  "error": {
    "code": 1,
    "message": "Invalid bead hash format"
  },
  "id": 1
}
```

### Common Error Codes

- **1**: Invalid input format/parsing error
- **2**: Internal server error (usually JSON serialization issues)
- **3**: Resource not found
- **4**: Validation error
- **5**: No data available
- **6**: Index out of bounds

## Implementation Notes

### Cohorts
Cohorts represent layered subgraphs in the braid DAG. They are indexed in reverse order where:
- Index 0 = most recent/latest cohort
- Index 1 = second-to-last cohort
- Index N = (N+1)th cohort from the end

### Genesis Beads
Genesis beads are the root nodes of the braid DAG - they have no parent beads. A braid can have multiple genesis beads.

### Tips
Tip beads are the leaf nodes of the braid DAG - they have no children beads. Tips represent the current "frontier" of the braid.

### Bead Hashes
All bead hashes are returned as hexadecimal strings for consistency and readability.

## Examples

### Basic Workflow
```bash
# 1. Check current state
curl -X POST http://127.0.0.1:6682 \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc": "2.0", "method": "getbeadcount", "params": [], "id": 1}'

# 2. Get current tips
curl -X POST http://127.0.0.1:6682 \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc": "2.0", "method": "gettips", "params": [], "id": 2}'

# 3. Get beads in latest cohort
curl -X POST http://127.0.0.1:6682 \
  -H "Content-Type: application/json" \
  -d '{"jsonrpc": "2.0", "method": "getbeadsincohort", "params": [0], "id": 3}'
```

### Batch Requests
JSON-RPC 2.0 supports batch requests:

```bash
curl -X POST http://127.0.0.1:6682 \
  -H "Content-Type: application/json" \
  -d '[
    {"jsonrpc": "2.0", "method": "getbeadcount", "params": [], "id": 1},
    {"jsonrpc": "2.0", "method": "getcohortcount", "params": [], "id": 2},
    {"jsonrpc": "2.0", "method": "gettips", "params": [], "id": 3}
  ]'
```
