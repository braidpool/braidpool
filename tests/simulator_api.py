from flask import Flask, send_from_directory
from flask_socketio import SocketIO
from flask_cors import CORS
import threading
import time
import sys
from simulator import main as run_simulator

app = Flask(__name__)
# Enable CORS for all routes - or limit it to the frontend only
CORS(app, resources={r"/*": {"origins": "*"}})

# SocketIO with CORS
socketio = SocketIO(app, cors_allowed_origins="*", logger=True, engineio_logger=True)

def run_simulator_live():
    while True:
        thickness = "250"
        for beads in range(1, 500):
            original_argv = sys.argv
            
            sys.argv = [
                "simulator.py",
                "-b",
                str(beads),
                "-A",
                "fixed",
                "-t",
                thickness,
                "-o",
                "braid",
            ]

            try:
                print(f"Running simulation with beads={beads}")
                run_simulator()
                
                try:
                    with open("braid.json", "r") as file:
                        data = file.read()
                    socketio.emit('braid_update', {'data': data})
                except FileNotFoundError:
                    print("braid.json not found yet")
                    
            finally:
                sys.argv = original_argv

            time.sleep(3)

@app.route('/braid.json')
def serve_braid():
    return send_from_directory('.', 'braid.json')

if __name__ == '__main__':
    # Start the simulator thread
    threading.Thread(target=run_simulator_live, daemon=True).start()
    
    # Run with host='0.0.0.0' to allow external connections
    socketio.run(app, host='0.0.0.0', port=65433, debug=True)