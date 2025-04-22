#!/usr/bin/env python3
import asyncio
import json
import websockets
import time
from simulator import print_hash

async def connect_to_server():
    uri = "ws://localhost:65433/ws"  # Note the /ws path
    print(f"Connecting to {uri}...")

    async with websockets.connect(
        uri,
        ping_interval=20,
        ping_timeout=30,
        additional_headers={"User-Agent": "BraidSimulatorClient/1.0"}
    ) as websocket:
        print("Connected to server")

        try:
            while True:
                # Receive message from server
                message = await websocket.recv()

                try:
                    data = json.loads(message)

                    if isinstance(data, dict) and data.get("type") == "message":
                        print(f"Received message: {data.get('data')}")
                    elif isinstance(data, dict) and data.get("type") == "braid_update":
                        handle_braid_update(data.get("data", {}))
                    else:
                        print(f"Received: {data}")
                except json.JSONDecodeError:
                    print(f"Received non-JSON message: {message}")

        except websockets.exceptions.ConnectionClosed:
            print("Connection closed")

def handle_braid_update(data):
    """Handle braid update data from the server"""
    if not data:
        return

    # Clear screen
    print("\033c")

    # Print parents
    print("Parents: {")
    for p in data.get('parents', {}):
        print(f"\t{print_hash(p)}: {print_hash(data['parents'][p])}")
    print("}")

    # Print cohorts
    print(f"Cohorts: [")
    for c in data.get('cohorts', []):
        print(f"\t{print_hash(c)}")
    print("]")

    # Print highest work path
    print(f"Highest Work Path: {print_hash(data.get('highest_work_path', []))}")
    print()

if __name__ == "__main__":
    try:
        # Run the async client
        asyncio.run(connect_to_server())
    except KeyboardInterrupt:
        print("Exiting...")
