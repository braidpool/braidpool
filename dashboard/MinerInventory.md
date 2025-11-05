# Miner Inventory Dashboard

The Miner Inventory Dashboard is a real-time monitoring system for cryptocurrency mining devices. It provides a comprehensive interface for tracking multiple miners' performance, health status, and operational metrics.

## Supported Mining Devices

The dashboard supports a wide range of ASIC miners through the pyasic library, including:

Currently supported mining devices can be found in the [pyasic documentation](https://docs.pyasic.org/en/latest/miners/supported_types/).


Note: The exact feature support may vary depending on the specific model and firmware version.

## Features

- Real-time miner monitoring
- Auto-refresh capability (default 30 seconds)
- Device status tracking (online/warning/offline)
- Comprehensive metrics display:
  - Hashrate (current and average)
  - Temperature monitoring
  - Power usage and efficiency
  - Fan speeds
  - Pool information
  - Error reporting

## Setup Requirements

### Frontend (Dashboard)
- Node.js (v14 or higher)
- React
- TypeScript
- Tailwind CSS

### Backend (API Server)
- Python 3.7+
- Flask
- pyasic library
- Flask-CORS

## Installation

### 1. API Server Setup

1. Navigate to the tests directory and install Python dependencies:
```bash
cd tests
pip install -r requirements.txt
```

2. Start the API server:
```bash
python miner_device.py
```
The server will run on port 5001 by default.

### 2. Dashboard Setup

1. Navigate to the dashboard directory:
```bash
cd dashboard
```

2. Install dependencies:
```bash
npm install
```

3. Start the development server:
```bash
npm run dev
```

## Configuration

### API Configuration
The dashboard communicates with miners through the API server. The API endpoint is configured in `URLs.ts`. By default, it points to:
```typescript
MINER_DEVICE_URL: 'http://localhost:5001'
```

## Usage
 **Adding Miners**
   - Enter the IP address of your miner in the input field
   - Click "Add Miner" or press Enter
   - The dashboard will attempt to connect and retrieve data from the miner
   - Make sure your miner is one of the supported devices listed above
   - Ensure the miner is on the same network and reachable from the dashboard
   - The miner should have its API access enabled (specific steps vary by manufacturer)



