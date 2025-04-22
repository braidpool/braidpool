#!/usr/bin/env python3
import unittest
import asyncio
import json
import websockets
import time
import subprocess
import signal
import os
from unittest.mock import patch, MagicMock
from simulator import print_hash

class TestSimulatorAPI(unittest.TestCase):
    """Test the Simulator API websocket connection and message handling."""

    @classmethod
    def setUpClass(cls):
        """Start the simulator API server for testing."""
        cls.server_process = subprocess.Popen(
            ["python", "simulator_api.py"],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE
        )
        # Give the server time to start
        time.sleep(1)
        pass

    @classmethod
    def tearDownClass(cls):
        """Stop the simulator API server after testing."""
        if hasattr(cls, 'server_process'):
            cls.server_process.send_signal(signal.SIGINT)
            cls.server_process.wait()

    def test_websocket_connection(self):
        """Test that we can connect to the websocket server."""
        async def test_connect():
            uri = "ws://localhost:65433"
            async with websockets.connect(uri) as ws:
                # Check that we received the welcome message
                message = await ws.recv()
                data = json.loads(message)
                self.assertEqual(data["type"], "message")
                self.assertEqual(data["data"], "Connected to braid simulator")

        asyncio.run(test_connect())

    def test_braid_data(self):
        async def test_connect():
            uri = "ws://localhost:65433"
            async with websockets.connect(uri) as ws:
                # Check that we received the welcome message
                message = await ws.recv()
                data = json.loads(message)
                self.assertEqual(data["type"], "message")
                self.assertEqual(data["data"], "Connected to braid simulator")

                message = await ws.recv()
                data = json.loads(message)
                self.assertEqual(data["type"], "braid_update")
                self.assertIn("data", data)
                self.assertIn("parents", data["data"])
                self.assertIn("cohorts", data["data"])
                self.assertIn("highest_work_path", data["data"])

        asyncio.run(test_connect())

if __name__ == "__main__":
    unittest.main()
