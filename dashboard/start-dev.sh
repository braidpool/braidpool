#!/bin/bash

# A script to manage the Braidpool development environment using tmux.
#
# This script provides a simple way to start, stop, and attach to all the
# services needed for local Braidpool development. It automatically handles
# checking dependencies and setting up the Python and Frontend environments.
#
# Usage:
#   ./start-dev.sh start   - Sets up environment and starts all services.
#   ./start-dev.sh stop    - Stops all services by killing the tmux session.
#   ./start-dev.sh attach  - Attaches to the running tmux session.

# --- Configuration ---
set -e # Exit immediately if a command exits with a non-zero status.

SESSION_NAME="braidpool-dev"
REQUIRED_PYTHON_VERSION="3.11.9"
TESTS_DIR="../tests"
VENV_DIR="$TESTS_DIR/.venv"

# Commands to run in each tmux window. These are defined after setup.
SIMULATOR_CMD="$VENV_DIR/bin/python $TESTS_DIR/simulator_api.py"
FRONTEND_CMD="npm run dev"

# --- Setup and Validation Functions ---

# Checks for all required command-line tools.
check_tool_deps() {
  echo "--- Checking for required tools ---"
  for tool in tmux python3 node; do
    if ! command -v $tool &>/dev/null; then
      echo "❌ Error: '$tool' is not installed. Please install it to continue." >&2
      if [ "$tool" == "tmux" ]; then
        echo "   For macOS: brew install tmux" >&2
        echo "   For Debian/Ubuntu: sudo apt-get install tmux" >&2
      elif [ "$tool" == "node" ]; then
        echo "   Node.js (which includes npm) is required. Install from https://nodejs.org/" >&2
      fi
      exit 1
    fi
    echo "✅ $tool is installed."
  done
}

# Checks if the python3 version is the exact required version.
check_python_version() {
  echo "Checking Python version..."
  # Get version string like "3.11.9"
  current_version=$(python3 --version 2>&1 | awk '{print $2}')

  if [ "$current_version" != "$REQUIRED_PYTHON_VERSION" ]; then
    echo "❌ Error: Python version mismatch." >&2
    echo "   Required: $REQUIRED_PYTHON_VERSION" >&2
    echo "   Found:    $current_version (from 'python3 --version')" >&2
    echo "   Please ensure 'python3' points to the correct installation." >&2
    exit 1
  fi
  echo "✅ Python version $current_version is compatible."
}

# Sets up the Python virtual environment and installs dependencies.
setup_python_env() {
  echo "--- Setting up Python environment ---"
  check_python_version

  if [ ! -d "$VENV_DIR" ]; then
    echo "Creating Python virtual environment in $VENV_DIR..."
    python3 -m venv "$VENV_DIR"
  else
    echo "Python virtual environment already exists."
  fi

  echo "Installing dependencies from requirements.txt..."
  # Directly call pip from the virtual environment to ensure correct isolation.
  # This avoids shell-specific 'source activate' commands and is more robust.
  "$VENV_DIR/bin/pip" install -r "$TESTS_DIR/requirements.txt"
  echo "✅ Python setup complete."
}

# Sets up the frontend environment.
setup_frontend_env() {
  echo "--- Setting up Frontend environment ---"
  echo "Installing frontend dependencies with npm..."
  npm install --prefix ../dashboard # --prefix ensures npm runs in the correct directory
  echo "✅ Frontend setup complete."
}

# --- Tmux Control Functions ---

# Function to start the development environment.
start() {
  if tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
    echo "Session '$SESSION_NAME' already exists."
    echo "Attach to it with: ./start-dev.sh attach"
    echo "Or stop it first with: ./start-dev.sh stop"
    exit 1
  fi

  # Run all setup steps first
  check_tool_deps
  setup_python_env
  setup_frontend_env

  echo "--- Starting services in tmux session '$SESSION_NAME' ---"

  # Create a new detached session for the Simulator
  tmux new-session -d -s "$SESSION_NAME" -n "Simulator" "$SIMULATOR_CMD"

  # Create a new window for the Frontend and select it
  tmux new-window -t "$SESSION_NAME" -n "Frontend" "$FRONTEND_CMD"
  tmux select-window -t "$SESSION_NAME:Frontend"

  echo ""
  echo "✅ Braidpool development environment started."
  echo "   Run './start-dev.sh attach' to view the services."
  echo "   Inside tmux, use 'Ctrl+b, n' to switch between windows (Simulator, Frontend)."
  echo "   Use 'Ctrl+b, d' to detach from the session (services keep running)."
}

# Function to stop the environment.
stop() {
  if tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
    echo "Stopping tmux session '$SESSION_NAME'..."
    tmux kill-session -t "$SESSION_NAME"
    echo "✅ Session stopped."
  else
    echo "Session '$SESSION_NAME' is not running."
  fi
}

# Function to attach to the session.
attach() {
  if ! tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
    echo "Session '$SESSION_NAME' is not running. Start it with './start-dev.sh start'"
    exit 1
  fi
  tmux attach-session -t "$SESSION_NAME"
}

# --- Main Script Logic ---
ACTION=${1:-"help"} # Default to "help" if no action is provided

case "$ACTION" in
start)
  start
  ;;
stop)
  stop
  ;;
attach)
  attach
  ;;
*)
  echo "Usage: $0 {start|stop|attach}"
  echo "Entrying into tmux session command : tmux attach -t braidpool-dev"
  exit 1
  ;;
esac
