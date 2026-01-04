#!/bin/bash

set -e # Exit immediately if a command exits with a non-zero status.

# --- Configuration ---
SESSION_NAME="braidpool"
REQUIRED_PYTHON_VERSION="3.12"
SCRIPT_DIR="$(cd -- "$(dirname -- "$0")" && pwd)"
REPO_DIR="$(cd -- "$SCRIPT_DIR/.." && pwd)"
DASHBOARD_DIR="$SCRIPT_DIR"
TESTS_DIR="$REPO_DIR/tests"
VENV_DIR="$TESTS_DIR/.venv"
API_DIR="$DASHBOARD_DIR/api"
MODE="dev" # Default frontend mode

# Commands to run in each tmux window. These are defined after setup.
SIMULATOR_CMD="$VENV_DIR/bin/python $TESTS_DIR/simulator_api.py"
API_CMD="node server.js"
FRONTEND_CMD="" # Set dynamically in start()

# --- Logging ---
# Unified logging function. Usage: log <LEVEL> "message"
# LEVEL can be: INFO, WARN, ERROR, or STEP
log() {
  local level="$1"
  local message="$2"
  local color_reset="[0m"
  local color_info="[0;32m"  # Green
  local color_warn="[0;33m"  # Yellow
  local color_error="[0;31m" # Red
  local color_step="[0;34m"  # Blue

  local color
  case "$level" in
  INFO) color="$color_info" ;;
  WARN) color="$color_warn" ;;
  ERROR) color="$color_error" ;;
  STEP) color="$color_step" ;;
  *) color="$color_reset" ;;
  esac

  if [ "$level" == "ERROR" ]; then
    >&2 echo -e "${color}[$(date +'%Y-%m-%d %H:%M:%S')] [$level] $message${color_reset}"
  else
    echo -e "${color}[$(date +'%Y-%m-%d %H:%M:%S')] [$level] $message${color_reset}"
  fi
}

# --- Setup and Validation Functions ---

check_tool_deps() {
  log "STEP" "Checking for required tools (tmux, python3, node, npm)..."
  for tool in tmux python3 node npm; do
    if ! command -v $tool &>/dev/null; then
      log "ERROR" "'$tool' is not installed. Please install it to continue."
      if [ "$tool" == "tmux" ]; then
        log "INFO" "For macOS: brew install tmux"
        log "INFO" "For Debian/Ubuntu: sudo apt-get install tmux"
      elif [ "$tool" == "node" ] || [ "$tool" == "npm" ]; then
        log "INFO" "Node.js (which includes npm) is required. Install from https://nodejs.org/"
      fi
      exit 1
    fi
    log "INFO" "✅ '$tool' is installed."
  done
}

check_python_version() {
  log "STEP" "Verifying Python version..."
  current_version=$(python3 --version 2>&1 | awk '{print $2}')

  if [[ ! "$current_version" == "$REQUIRED_PYTHON_VERSION"* ]]; then
    log "ERROR" "Python version mismatch."
    log "ERROR" "  Required: $REQUIRED_PYTHON_VERSION.*"
    log "ERROR" "  Found:    $current_version (from 'python3 --version')"
    log "ERROR" "  Please ensure 'python3' points to the correct installation."
    exit 1
  fi
  log "INFO" "✅ Python version $current_version is compatible."
}

setup_python_env() {
  log "STEP" "Setting up Python environment..."
  check_python_version

  if [ ! -d "$VENV_DIR" ]; then
    log "INFO" "Creating Python virtual environment in '$VENV_DIR'..."
    python3 -m venv "$VENV_DIR"
    log "INFO" "✅ Virtual environment created."
  else
    log "INFO" "Python virtual environment already exists."
  fi

  log "INFO" "Installing dependencies from '$TESTS_DIR/requirements.txt'..."
  "$VENV_DIR/bin/pip" install -r "$TESTS_DIR/requirements.txt"
  log "INFO" "✅ Python dependencies are up to date."
}

setup_frontend_env() {
  log "STEP" "Setting up Frontend environment..."
  log "INFO" "Installing frontend dependencies from '$DASHBOARD_DIR/package.json'..."
  npm install --prefix "$DASHBOARD_DIR"
  log "INFO" "✅ Frontend dependencies are up to date."
}

setup_api_env() {
  log "STEP" "Setting up API environment..."
  log "INFO" "Installing API dependencies from '$API_DIR/package.json'..."
  npm install --prefix "$API_DIR"
  log "INFO" "✅ API dependencies are up to date."

  if [ ! -f "$API_DIR/.env" ]; then
    log "WARN" "API '.env' file not found. Creating from '.env.example'..."
    if [ -f "$API_DIR/.env.example" ]; then
      cp "$API_DIR/.env.example" "$API_DIR/.env"
      log "WARN" "✅ '.env' file created. Please edit '$API_DIR/.env' to set your RPC_PASS."
    else
      log "WARN" "'.env.example' not found in '$API_DIR'. Skipping .env creation."
    fi
  else
    log "INFO" "API '.env' file already exists."
  fi
}

# --- Argument Parsing ---

parse_start_flags() {
  MODE=${MODE:-dev}

  while [ $# -gt 0 ]; do
    case "$1" in
    --mode)
      MODE="$2"
      shift 2
      ;;
    --mode=*)
      MODE="${1#*=}"
      shift
      ;;
    *)
      shift
      ;;
    esac
  done

  case "$MODE" in
  dev | prod)
    log "INFO" "Frontend mode set to '$MODE'."
    ;;
  "")
    if [ -t 0 ]; then
      read -r -p "Choose frontend mode (dev/prod) [dev]: " _input
      MODE="${_input:-dev}"
    else
      MODE="dev"
    fi
    ;;
  *)
    log "ERROR" "Invalid mode: '$MODE'. Use 'dev' or 'prod'."
    exit 1
    ;;
  esac
}

# --- Tmux Control Functions ---

start() {
  parse_start_flags "$@"

  if tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
    log "WARN" "Session '$SESSION_NAME' already exists."
    log "INFO" "To attach, run: ./start.sh attach"
    log "INFO" "To stop, run: ./start.sh stop"
    exit 1
  fi

  log "STEP" "Starting Braidpool development environment..."
  check_tool_deps
  setup_python_env
  setup_frontend_env
  setup_api_env

  log "STEP" "Starting services in tmux session '$SESSION_NAME'..."

  log "INFO" "Starting Simulator in window 'Simulator'..."
  tmux new-session -d -s "$SESSION_NAME" -n "Simulator" -c "$REPO_DIR" "$SIMULATOR_CMD"

  log "INFO" "Starting API server in window 'API'..."
  tmux new-window -t "$SESSION_NAME" -n "API" -c "$API_DIR" "$API_CMD"

  if [ "$MODE" = "prod" ]; then
    log "INFO" "Building frontend for production... This may take a moment."
    npm run build --prefix "$DASHBOARD_DIR"
    FRONTEND_CMD="npm run preview"
    log "INFO" "Starting Frontend (production preview) in window 'Frontend'..."
  else
    FRONTEND_CMD="npm run dev"
    log "INFO" "Starting Frontend (development server) in window 'Frontend'..."
  fi

  tmux new-window -t "$SESSION_NAME" -n "Frontend" -c "$DASHBOARD_DIR" "$FRONTEND_CMD"
  tmux select-window -t "$SESSION_NAME:Frontend"

  log "INFO" "✅ Braidpool environment started successfully."
  log "INFO" "   - Session: $SESSION_NAME"
  log "INFO" "   - Frontend Mode: $MODE"
  log "INFO" "   - Get into Sesssion by Command : tmux attach -t braidpool"
  log "INFO" "   - Windows: Simulator, API, Frontend"
  log "INFO" "To attach to the session, run: ./start.sh attach"
  log "INFO" "Inside tmux, use 'Ctrl+b, n' to switch windows."
  log "INFO" "Use 'Ctrl+b, d' to detach (services keep running)."
}

stop() {
  log "STEP" "Stopping Braidpool environment..."
  if tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
    log "INFO" "Found running session '$SESSION_NAME'. Terminating..."
    tmux kill-session -t "$SESSION_NAME"
    log "INFO" "✅ Session '$SESSION_NAME' stopped."
  else
    log "WARN" "No running session named '$SESSION_NAME' found."
  fi
}

attach() {
  if ! tmux has-session -t "$SESSION_NAME" 2>/dev/null; then
    log "ERROR" "Session '$SESSION_NAME' is not running. Start it with './start.sh start'"
    exit 1
  fi
  log "INFO" "Attaching to tmux session '$SESSION_NAME'..."
  tmux attach-session -t "$SESSION_NAME"
}

# --- Main Script Logic ---
ACTION=${1:-"help"}

case "$ACTION" in
start)
  shift
  start "$@"
  ;;
stop)
  stop
  ;;
attach)
  attach
  ;;
*)
  echo "Usage: $0 {start|stop|attach} [--mode dev|prod]"
  echo "Commands:"
  echo "  start [--mode dev|prod]  - Sets up and starts all services in a new tmux session."
  echo "  stop                     - Stops the tmux session and all running services."
  echo "  attach                   - Attaches to the running tmux session."
  echo "Example:"
  echo "  ./start.sh start --mode prod"
  exit 1
  ;;
esac

