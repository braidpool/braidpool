#!/usr/bin/env python3
import socketio
import time
from simulator import print_hash

# Create a Socket.IO client
sio = socketio.Client()

@sio.event
def connect():
    print("Connected to server")

@sio.event
def disconnect():
    print("Disconnected from server")

@sio.on('message')
def on_message(data):
    print(f"Received message: {data}")

@sio.on('braid_update')
def on_braid_update(data):
    #print("\033[2J\033[H") # clear screen
    print("\033c") # clear screen
    print("Parents: {")
    for p in data['parents']:
        print(f"\t{print_hash(p)}: {print_hash(data['parents'][p])}")
    print("}")
    print(f"Cohorts: [")
    for c in data['cohorts']:
        print(f"\t{print_hash(c)}")
    print("]")
    print(f"Highest Work Path: {print_hash(data['highest_work_path'])}")
    print()

if __name__ == "__main__":
    try:
        # Connect to the Socket.IO server
        sio.connect('http://localhost:65433')

        # Keep the script running
        while True:
            time.sleep(1)
    except KeyboardInterrupt:
        print("Exiting...")
    finally:
        if sio.connected:
            sio.disconnect()
